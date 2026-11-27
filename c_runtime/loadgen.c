#define _POSIX_C_SOURCE 200809L
#define _DARWIN_C_SOURCE 1

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <errno.h>
#include <time.h>
#include <unistd.h>
#include <fcntl.h>
#include <poll.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/resource.h>
#include <netinet/in.h>
#include <arpa/inet.h>

#ifdef __APPLE__
#include <mach/mach.h>
#endif

#include <lean/lean.h>
#include "swim_exports.h"

lean_object* initialize_SwimCore(uint8_t builtin, lean_object* world) {
    (void)world;
    return initialize_swim_SwimCore(builtin);
}

static uint64_t now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

static uint64_t now_ms(void) {
    return now_ns() / 1000000ULL;
}

static void sleep_us(uint64_t us) {
    struct timespec req;
    req.tv_sec = (time_t)(us / 1000000ULL);
    req.tv_nsec = (long)((us % 1000000ULL) * 1000ULL);
    nanosleep(&req, NULL);
}

static size_t get_current_rss_bytes(void) {
#ifdef __APPLE__
    struct mach_task_basic_info info;
    mach_msg_type_number_t count = MACH_TASK_BASIC_INFO_COUNT;
    if (task_info(mach_task_self(), MACH_TASK_BASIC_INFO, (task_info_t)&info, &count) == KERN_SUCCESS) {
        return (size_t)info.resident_size;
    }
#endif
    FILE* f = fopen("/proc/self/statm", "r");
    if (f) {
        unsigned long size_pages = 0, rss_pages = 0;
        if (fscanf(f, "%lu %lu", &size_pages, &rss_pages) == 2) {
            fclose(f);
            long page_sz = sysconf(_SC_PAGESIZE);
            return (size_t)rss_pages * (size_t)(page_sz > 0 ? page_sz : 4096);
        }
        fclose(f);
    }
    struct rusage ru;
    if (getrusage(RUSAGE_SELF, &ru) == 0) {
#ifdef __APPLE__
        return (size_t)ru.ru_maxrss;
#else
        return (size_t)ru.ru_maxrss * 1024ULL;
#endif
    }
    return 0;
}

static uint64_t splitmix64(uint64_t* state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

static void write_u32_be(uint8_t* p, uint32_t v) {
    p[0] = (uint8_t)((v >> 24) & 0xFF);
    p[1] = (uint8_t)((v >> 16) & 0xFF);
    p[2] = (uint8_t)((v >> 8) & 0xFF);
    p[3] = (uint8_t)(v & 0xFF);
}

static uint32_t read_u32_be(const uint8_t* p) {
    return ((uint32_t)p[0] << 24) | ((uint32_t)p[1] << 16) |
           ((uint32_t)p[2] << 8)  | (uint32_t)p[3];
}

typedef struct {
    uint32_t id;
    uint8_t  status;
    uint32_t inc;
    uint8_t  tx;
} WireUpdate;

/* Encode SWIM Ping (1) / Ack (2) / PingReq (3) frame matching SwimCore/Wire.lean */
static size_t encode_swim_msg(uint8_t* buf, uint8_t msg_type, uint32_t src_id,
                              uint32_t seq, uint32_t target_id,
                              const WireUpdate* updates, uint8_t count) {
    size_t pos = 0;
    buf[pos++] = msg_type;
    write_u32_be(buf + pos, src_id); pos += 4;
    write_u32_be(buf + pos, seq);    pos += 4;
    if (msg_type == 3) {
        write_u32_be(buf + pos, target_id); pos += 4;
    }
    buf[pos++] = count;
    for (uint8_t i = 0; i < count; i++) {
        write_u32_be(buf + pos, updates[i].id);  pos += 4;
        buf[pos++] = updates[i].status;
        write_u32_be(buf + pos, updates[i].inc); pos += 4;
        buf[pos++] = updates[i].tx;
    }
    return pos;
}

static size_t generate_fuzz_frame(uint8_t* buf, size_t max_len, uint64_t* rng) {
    uint64_t r = splitmix64(rng);
    size_t mode = (size_t)(r % 5ULL);
    if (mode == 0) {
        /* Undersized header (< 10 bytes) */
        size_t len = (size_t)((r >> 8) % 9ULL);
        for (size_t i = 0; i < len && i < max_len; i++) {
            buf[i] = (uint8_t)(splitmix64(rng) & 0xFF);
        }
        return len;
    } else if (mode == 1) {
        /* Invalid message type tag */
        buf[0] = (uint8_t)(4 + ((r >> 16) % 250ULL));
        for (size_t i = 1; i < 16 && i < max_len; i++) {
            buf[i] = (uint8_t)(splitmix64(rng) & 0xFF);
        }
        return 16;
    } else if (mode == 2) {
        /* Truncated packet claiming many gossip updates */
        size_t n = encode_swim_msg(buf, 1, 9001, (uint32_t)r, 0, NULL, 0);
        buf[9] = 42; /* Claim 42 updates while payload has 0 */
        return n;
    } else if (mode == 3) {
        /* Invalid status byte (status = 3..255) inside update */
        WireUpdate u = { 2, (uint8_t)(3 + ((r >> 8) % 200ULL)), 1, 1 };
        return encode_swim_msg(buf, 1, 9001, (uint32_t)r, 0, &u, 1);
    } else {
        /* Overlong/corrupted PingReq payload */
        size_t len = 14 + (size_t)((r >> 20) % 40ULL);
        if (len > max_len) len = max_len;
        buf[0] = 3;
        for (size_t i = 1; i < len; i++) {
            buf[i] = (uint8_t)(splitmix64(rng) & 0xFF);
        }
        buf[13] = 250; /* Invalid count mismatch */
        return len;
    }
}

static int cmp_u64(const void* a, const void* b) {
    uint64_t va = *(const uint64_t*)a;
    uint64_t vb = *(const uint64_t*)b;
    return (va > vb) - (va < vb);
}

static uint64_t percentile_u64(const uint64_t* sorted, size_t n, double p) {
    if (n == 0) return 0;
    size_t idx = (size_t)(p * (double)(n - 1));
    if (idx >= n) idx = n - 1;
    return sorted[idx];
}

/* ---------- Experiment 1: Direct Perceus C FFI Stress & Invariant Verification ---------- */
static int run_ffi_experiment(size_t num_ops, size_t num_peers, uint64_t seed) {
    printf("=== [Experiment 1] Direct Lean-4 Perceus C FFI Load & Safety Verification ===\n");
    printf("Config: ops=%zu, cluster_peers=%zu, fuzz_ratio=25%%, seed=0x%llx\n",
           num_ops, num_peers, (unsigned long long)seed);

    lean_object* state = swim_init_node(1, 0x7F000001U, 19300, seed);
    for (size_t i = 0; i < num_peers; i++) {
        uint32_t peer_id = (uint32_t)(i + 2);
        state = swim_add_peer(state, peer_id, 0x7F000001U, (uint16_t)(19301 + i));
    }

    uint64_t* lat_ns = (uint64_t*)calloc(num_ops, sizeof(uint64_t));
    if (!lat_ns) {
        fprintf(stderr, "OOM allocating latency array\n");
        lean_dec(state);
        return 1;
    }

    lean_inc(state);
    uint32_t expected_peers = swim_members_size(state);
    lean_inc(state);
    uint32_t prev_inc = swim_self_incarnation(state);
    size_t rss_start = get_current_rss_bytes();
    size_t rss_mid = rss_start;

    uint64_t rng = seed ^ 0xA5A5A5A5A5A5A5A5ULL;
    uint64_t sim_now_ms = 1000;
    uint8_t pkt_buf[256];

    size_t valid_pkt_ops = 0;
    size_t fuzz_pkt_ops = 0;
    size_t tick_ops = 0;
    size_t refutations = 0;
    size_t actions_emitted = 0;

    uint64_t t_bench_start = now_ns();

    for (size_t op = 0; op < num_ops; op++) {
        if (op == num_ops / 2) {
            rss_mid = get_current_rss_bytes();
        }

        uint64_t r = splitmix64(&rng);
        uint64_t kind = r % 20ULL;
        lean_object* res = NULL;
        uint64_t t0 = 0, t1 = 0;

        if (kind == 0) {
            /* 5%: Periodic tick driving probe / suspect timeout logic */
            sim_now_ms += 50;
            t0 = now_ns();
            res = swim_step_tick(state, sim_now_ms);
            t1 = now_ns();
            tick_ops++;
        } else if (kind <= 5) {
            /* 25%: Malformed / fuzzed packets testing decodeMessage safety boundary */
            size_t len = generate_fuzz_frame(pkt_buf, sizeof(pkt_buf), &rng);
            lean_object* payload = lean_alloc_sarray(1, len, len);
            if (len > 0) memcpy(lean_sarray_cptr(payload), pkt_buf, len);
            t0 = now_ns();
            res = swim_step_packet(state, 0x7F000001U, 19399, payload, sim_now_ms);
            t1 = now_ns();
            fuzz_pkt_ops++;
        } else {
            /* 70%: Valid SWIM Ping / PingReq with piggybacked gossip & periodic refutation */
            uint32_t src_id = (uint32_t)(2 + (r % num_peers));
            WireUpdate updates[4];
            uint8_t u_cnt = (uint8_t)((r >> 8) % 4ULL);
            for (uint8_t u = 0; u < u_cnt; u++) {
                uint64_t ru = splitmix64(&rng);
                if ((op % 500 == 0) && u == 0) {
                    /* Inject self-suspicion with current incarnation to exercise refutation */
                    updates[u].id = 1;
                    updates[u].status = 1; /* Suspect */
                    updates[u].inc = prev_inc;
                    updates[u].tx = 3;
                } else {
                    updates[u].id = (uint32_t)(2 + (ru % num_peers));
                    updates[u].status = 0; /* Alive gossip keeps cluster active */
                    updates[u].inc = prev_inc;
                    updates[u].tx = 2;
                }
            }
            uint8_t msg_type = (kind == 6) ? 3 : 1;
            uint32_t target = (uint32_t)(2 + ((r >> 16) % num_peers));
            size_t len = encode_swim_msg(pkt_buf, msg_type, src_id, (uint32_t)op, target, updates, u_cnt);
            lean_object* payload = lean_alloc_sarray(1, len, len);
            memcpy(lean_sarray_cptr(payload), pkt_buf, len);
            t0 = now_ns();
            res = swim_step_packet(state, 0x7F000001U, (uint16_t)(19300 + src_id), payload, sim_now_ms);
            t1 = now_ns();
            valid_pkt_ops++;
        }

        lat_ns[op] = t1 - t0;

        lean_object* new_state = lean_ctor_get(res, 0);
        lean_inc(new_state);
        lean_object* actions = lean_ctor_get(res, 1);
        lean_inc(actions);
        lean_dec(res);

        lean_inc(actions);
        actions_emitted += (size_t)swim_actions_size(actions);
        lean_dec(actions);

        state = new_state;

        /* Observe Refinement.step_preserves_safety invariants at runtime */
        lean_inc(state);
        uint32_t cur_peers = swim_members_size(state);
        lean_inc(state);
        uint32_t cur_inc = swim_self_incarnation(state);

        if (cur_peers != expected_peers) {
            fprintf(stderr, "SAFETY VIOLATION at op=%zu: members_size changed %u -> %u\n",
                    op, expected_peers, cur_peers);
            free(lat_ns);
            lean_dec(state);
            return 1;
        }
        if (cur_inc < prev_inc) {
            fprintf(stderr, "SAFETY VIOLATION at op=%zu: incarnation decreased %u -> %u\n",
                    op, prev_inc, cur_inc);
            free(lat_ns);
            lean_dec(state);
            return 1;
        }
        if (cur_inc > prev_inc) {
            refutations++;
            prev_inc = cur_inc;
        }
    }

    uint64_t t_bench_end = now_ns();
    size_t rss_end = get_current_rss_bytes();
    double elapsed_s = (double)(t_bench_end - t_bench_start) / 1e9;
    double throughput = (double)num_ops / elapsed_s;

    qsort(lat_ns, num_ops, sizeof(uint64_t), cmp_u64);
    uint64_t p50 = percentile_u64(lat_ns, num_ops, 0.50);
    uint64_t p95 = percentile_u64(lat_ns, num_ops, 0.95);
    uint64_t p99 = percentile_u64(lat_ns, num_ops, 0.99);
    uint64_t p999 = percentile_u64(lat_ns, num_ops, 0.999);
    uint64_t pmax = lat_ns[num_ops - 1];

    printf("Observed FFI Results:\n");
    printf("  Total transitions : %zu (valid=%zu, fuzz=%zu, tick=%zu) in %.3fs\n",
           num_ops, valid_pkt_ops, fuzz_pkt_ops, tick_ops, elapsed_s);
    printf("  Throughput        : %.0f transitions/sec\n", throughput);
    printf("  Transition latency: p50=%lluns  p95=%lluns  p99=%lluns  p99.9=%lluns  max=%lluns\n",
           (unsigned long long)p50, (unsigned long long)p95, (unsigned long long)p99,
           (unsigned long long)p999, (unsigned long long)pmax);
    printf("  Safety invariants : %zu/%zu verified (peers=%u invariant, final_inc=%u, refutations=%zu)\n",
           num_ops, num_ops, expected_peers, prev_inc, refutations);
    printf("  Actions generated : %zu\n", actions_emitted);
    printf("  Process RSS (MiB) : start=%.2f -> mid(50%%)=%.2f -> end(100%%)=%.2f\n",
           (double)rss_start / (1024.0 * 1024.0),
           (double)rss_mid / (1024.0 * 1024.0),
           (double)rss_end / (1024.0 * 1024.0));

    free(lat_ns);
    lean_dec(state);
    return 0;
}

/* ---------- Experiment 2: Live UDP Ping/Ack + Fuzz Load Generator ---------- */
static int create_client_udp_socket(void) {
    int fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) {
        perror("loadgen socket");
        return -1;
    }
    int flags = fcntl(fd, F_GETFL, 0);
    if (flags < 0 || fcntl(fd, F_SETFL, flags | O_NONBLOCK) < 0) {
        perror("loadgen fcntl");
        close(fd);
        return -1;
    }
    int buf_sz = 1024 * 1024;
    (void)setsockopt(fd, SOL_SOCKET, SO_RCVBUF, &buf_sz, sizeof(buf_sz));
    (void)setsockopt(fd, SOL_SOCKET, SO_SNDBUF, &buf_sz, sizeof(buf_sz));
    return fd;
}

static int run_udp_experiment(const char* ip, uint16_t port, size_t total_pings,
                              size_t fuzz_every, size_t window, uint64_t seed) {
    printf("=== [Experiment 2] Live UDP Network Load Generator against swim_node ===\n");
    printf("Target: %s:%u | pings=%zu | window=%zu | fuzz_every=%zu\n",
           ip, port, total_pings, window, fuzz_every);

    int fd = create_client_udp_socket();
    if (fd < 0) return 1;

    struct sockaddr_in dst;
    memset(&dst, 0, sizeof(dst));
    dst.sin_family = AF_INET;
    dst.sin_port = htons(port);
    if (inet_pton(AF_INET, ip, &dst.sin_addr) <= 0) {
        fprintf(stderr, "Invalid IP: %s\n", ip);
        close(fd);
        return 1;
    }

    uint64_t* send_ts = (uint64_t*)calloc(total_pings, sizeof(uint64_t));
    bool*     acked   = (bool*)calloc(total_pings, sizeof(bool));
    uint64_t* rtt_ns  = (uint64_t*)calloc(total_pings, sizeof(uint64_t));
    if (!send_ts || !acked || !rtt_ns) {
        fprintf(stderr, "OOM in UDP loadgen\n");
        free(send_ts); free(acked); free(rtt_ns);
        close(fd);
        return 1;
    }

    uint64_t rng = seed;
    size_t sent_pings = 0;
    size_t acked_count = 0;
    size_t malformed_sent = 0;
    size_t unexpected_packets = 0;
    uint64_t bytes_tx = 0;
    uint64_t bytes_rx = 0;

    uint8_t tx_buf[256];
    uint8_t rx_buf[4096];

    uint64_t t_start = now_ns();
    uint64_t last_progress_ns = t_start;

    while (sent_pings < total_pings || acked_count < sent_pings) {
        /* Top up in-flight window */
        while (sent_pings < total_pings && (sent_pings - acked_count) < window) {
            if (fuzz_every > 0 && (sent_pings % fuzz_every == (fuzz_every - 1))) {
                size_t flen = generate_fuzz_frame(tx_buf, sizeof(tx_buf), &rng);
                ssize_t s = sendto(fd, tx_buf, flen, 0, (struct sockaddr*)&dst, sizeof(dst));
                if (s >= 0) {
                    bytes_tx += (uint64_t)s;
                    malformed_sent++;
                }
            }

            WireUpdate up = { 9999, 0, 0, 1 };
            uint8_t u_cnt = (sent_pings % 3 == 0) ? 1 : 0;
            size_t len = encode_swim_msg(tx_buf, 1, 9999, (uint32_t)sent_pings, 0, &up, u_cnt);
            send_ts[sent_pings] = now_ns();
            ssize_t n = sendto(fd, tx_buf, len, 0, (struct sockaddr*)&dst, sizeof(dst));
            if (n < 0) {
                if (errno == EAGAIN || errno == EWOULDBLOCK || errno == ENOBUFS) {
                    break;
                }
                perror("loadgen sendto");
                break;
            }
            bytes_tx += (uint64_t)n;
            sent_pings++;
        }

        /* Poll briefly for Ack responses */
        struct pollfd pfd;
        pfd.fd = fd;
        pfd.events = POLLIN;
        pfd.revents = 0;
        int pr = poll(&pfd, 1, 10);
        if (pr > 0 && (pfd.revents & POLLIN)) {
            while (1) {
                ssize_t rn = recvfrom(fd, rx_buf, sizeof(rx_buf), 0, NULL, NULL);
                if (rn < 0) {
                    if (errno == EAGAIN || errno == EWOULDBLOCK) break;
                    if (errno == EINTR) continue;
                    break;
                }
                bytes_rx += (uint64_t)rn;
                uint64_t t_rx = now_ns();
                if (rn >= 10 && rx_buf[0] == 2) {
                    uint32_t ack_seq = read_u32_be(rx_buf + 5);
                    if ((size_t)ack_seq < sent_pings && !acked[ack_seq]) {
                        acked[ack_seq] = true;
                        rtt_ns[acked_count++] = t_rx - send_ts[ack_seq];
                        last_progress_ns = t_rx;
                    }
                } else {
                    unexpected_packets++;
                }
            }
        }

        /* Drain deadline if tail UDP packets dropped on loopback */
        if (sent_pings == total_pings && (now_ns() - last_progress_ns) > 500000000ULL) {
            break;
        }
    }

    uint64_t t_end = now_ns();
    double elapsed_s = (double)(t_end - t_start) / 1e9;
    double rps = (double)acked_count / elapsed_s;
    double mbps_tx = ((double)bytes_tx * 8.0) / (elapsed_s * 1e6);
    double mbps_rx = ((double)bytes_rx * 8.0) / (elapsed_s * 1e6);

    qsort(rtt_ns, acked_count, sizeof(uint64_t), cmp_u64);
    double p50_us  = (double)percentile_u64(rtt_ns, acked_count, 0.50) / 1e3;
    double p95_us  = (double)percentile_u64(rtt_ns, acked_count, 0.95) / 1e3;
    double p99_us  = (double)percentile_u64(rtt_ns, acked_count, 0.99) / 1e3;
    double pmax_us = (acked_count > 0) ? ((double)rtt_ns[acked_count - 1] / 1e3) : 0.0;

    printf("Observed UDP Load Results:\n");
    printf("  Roundtrips  : %zu / %zu acked (loss=%.3f%%) in %.3fs\n",
           acked_count, sent_pings,
           sent_pings > 0 ? 100.0 * (double)(sent_pings - acked_count) / (double)sent_pings : 0.0,
           elapsed_s);
    printf("  Fuzz frames : %zu malformed UDP frames injected (unexpected replies=%zu)\n",
           malformed_sent, unexpected_packets);
    printf("  Throughput  : %.0f roundtrips/sec | TX=%.2f Mbps | RX=%.2f Mbps\n",
           rps, mbps_tx, mbps_rx);
    printf("  Wire RTT    : p50=%.1f us  p95=%.1f us  p99=%.1f us  max=%.1f us\n",
           p50_us, p95_us, p99_us, pmax_us);

    free(send_ts);
    free(acked);
    free(rtt_ns);
    close(fd);

    /* Require >= 99% ACK completion under local loopback load */
    if (acked_count * 100 < sent_pings * 99) {
        fprintf(stderr, "FAIL: Excessive packet loss in UDP experiment (%zu / %zu acked)\n",
                acked_count, sent_pings);
        return 1;
    }
    return 0;
}

/* ---------- Experiment 3: Continuous Background UDP Storm During Cluster Churn ---------- */
static int run_storm_experiment(const char* ip, uint16_t base_port, size_t n_nodes,
                                uint64_t duration_ms, uint64_t target_pps, uint64_t seed) {
    printf("=== [Experiment 3] Concurrent Cluster Churn Background Storm ===\n");
    printf("Blasting %s ports %u..%u (~%llu pps + malformed fuzz) for %llums\n",
           ip, base_port, (unsigned)(base_port + n_nodes - 1),
           (unsigned long long)target_pps, (unsigned long long)duration_ms);

    int fd = create_client_udp_socket();
    if (fd < 0) return 1;

    struct sockaddr_in addrs[16];
    if (n_nodes == 0 || n_nodes > 16) {
        close(fd);
        return 1;
    }
    for (size_t i = 0; i < n_nodes; i++) {
        memset(&addrs[i], 0, sizeof(addrs[i]));
        addrs[i].sin_family = AF_INET;
        addrs[i].sin_port = htons((uint16_t)(base_port + i));
        inet_pton(AF_INET, ip, &addrs[i].sin_addr);
    }

    uint64_t rng = seed;
    uint8_t tx_buf[256];
    uint8_t rx_buf[4096];
    uint64_t t_end_ms = now_ms() + duration_ms;
    size_t tx_valid = 0, tx_fuzz = 0, rx_acks = 0;
    uint32_t seq = 1;

    uint64_t batch = (target_pps >= 1000) ? (target_pps / 200) : 5;
    if (batch < 1) batch = 1;

    while (now_ms() < t_end_ms) {
        for (uint64_t b = 0; b < batch; b++) {
            size_t idx = (size_t)(seq % n_nodes);
            if (seq % 10 == 0) {
                size_t flen = generate_fuzz_frame(tx_buf, sizeof(tx_buf), &rng);
                if (sendto(fd, tx_buf, flen, 0, (struct sockaddr*)&addrs[idx], sizeof(addrs[idx])) >= 0) {
                    tx_fuzz++;
                }
            } else {
                size_t len = encode_swim_msg(tx_buf, 1, 9998, seq, 0, NULL, 0);
                if (sendto(fd, tx_buf, len, 0, (struct sockaddr*)&addrs[idx], sizeof(addrs[idx])) >= 0) {
                    tx_valid++;
                }
            }
            seq++;
        }

        while (1) {
            ssize_t rn = recvfrom(fd, rx_buf, sizeof(rx_buf), 0, NULL, NULL);
            if (rn <= 0) break;
            if (rn >= 10 && rx_buf[0] == 2) rx_acks++;
        }
        sleep_us(5000);
    }

    printf("Storm Complete: valid_pings=%zu, fuzz_frames=%zu, acks_observed=%zu\n",
           tx_valid, tx_fuzz, rx_acks);
    close(fd);
    return (rx_acks > 0) ? 0 : 1;
}

static void print_usage(const char* prog) {
    printf("Usage:\n");
    printf("  %s --mode ffi [--ops N] [--peers P] [--seed S]\n", prog);
    printf("  %s --mode udp [--ip IP] [--port PORT] [--ops N] [--window W] [--fuzz-every K]\n", prog);
    printf("  %s --mode storm [--ip IP] [--port BASE_PORT] [--nodes N] [--duration-ms MS] [--pps P]\n", prog);
}

int main(int argc, char* argv[]) {
    const char* mode = "ffi";
    const char* ip = "127.0.0.1";
    uint16_t port = 19301;
    size_t ops = 200000;
    size_t peers = 100;
    size_t nodes = 4;
    size_t window = 16;
    size_t fuzz_every = 10;
    uint64_t duration_ms = 6500;
    uint64_t pps = 4000;
    uint64_t seed = 0x20261127CAFEBABEULL;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--mode") == 0 && i + 1 < argc) mode = argv[++i];
        else if (strcmp(argv[i], "--ip") == 0 && i + 1 < argc) ip = argv[++i];
        else if (strcmp(argv[i], "--port") == 0 && i + 1 < argc) port = (uint16_t)strtoul(argv[++i], NULL, 10);
        else if (strcmp(argv[i], "--ops") == 0 && i + 1 < argc) ops = (size_t)strtoull(argv[++i], NULL, 10);
        else if (strcmp(argv[i], "--peers") == 0 && i + 1 < argc) peers = (size_t)strtoull(argv[++i], NULL, 10);
        else if (strcmp(argv[i], "--nodes") == 0 && i + 1 < argc) nodes = (size_t)strtoull(argv[++i], NULL, 10);
        else if (strcmp(argv[i], "--window") == 0 && i + 1 < argc) window = (size_t)strtoull(argv[++i], NULL, 10);
        else if (strcmp(argv[i], "--fuzz-every") == 0 && i + 1 < argc) fuzz_every = (size_t)strtoull(argv[++i], NULL, 10);
        else if (strcmp(argv[i], "--duration-ms") == 0 && i + 1 < argc) duration_ms = strtoull(argv[++i], NULL, 10);
        else if (strcmp(argv[i], "--pps") == 0 && i + 1 < argc) pps = strtoull(argv[++i], NULL, 10);
        else if (strcmp(argv[i], "--seed") == 0 && i + 1 < argc) seed = strtoull(argv[++i], NULL, 16);
        else if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
            print_usage(argv[0]);
            return 0;
        }
    }

    lean_initialize_runtime_module();
    lean_object* world = lean_io_mk_world();
    lean_object* init_res = initialize_SwimCore(1, world);
    if (lean_io_result_is_error(init_res)) {
        fprintf(stderr, "Fatal error initializing SwimCore\n");
        lean_dec_ref(init_res);
        return 1;
    }
    lean_dec_ref(init_res);

    if (strcmp(mode, "ffi") == 0) {
        return run_ffi_experiment(ops, peers, seed);
    } else if (strcmp(mode, "udp") == 0) {
        return run_udp_experiment(ip, port, ops, fuzz_every, window, seed);
    } else if (strcmp(mode, "storm") == 0) {
        return run_storm_experiment(ip, port, nodes, duration_ms, pps, seed);
    } else {
        fprintf(stderr, "Unknown mode: %s\n", mode);
        print_usage(argv[0]);
        return 1;
    }
}
