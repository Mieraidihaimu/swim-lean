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
#include <signal.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>

#include <lean/lean.h>
#include "swim_exports.h"

/* Wrapper providing initialize_SwimCore signature */
lean_object* initialize_SwimCore(uint8_t builtin, lean_object* world) {
    (void)world;
    return initialize_swim_SwimCore(builtin);
}

static volatile sig_atomic_t g_running = 1;

static void handle_signal(int sig) {
    (void)sig;
    g_running = 0;
}

static uint64_t get_monotonic_time_ms(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) {
        perror("[SWIM-C] clock_gettime");
        return 0;
    }
    return (uint64_t)ts.tv_sec * 1000ULL + (uint64_t)ts.tv_nsec / 1000000ULL;
}

static void ip_to_str(uint32_t ip, char* buf, size_t buf_len) {
    struct in_addr in;
    in.s_addr = htonl(ip);
    inet_ntop(AF_INET, &in, buf, (socklen_t)buf_len);
}

static int create_udp_socket(const char* bind_ip_str, uint16_t port) {
    int fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) {
        perror("[SWIM-C] socket(AF_INET, SOCK_DGRAM, 0)");
        return -1;
    }

    /* Configure non-blocking mode with fcntl */
    int flags = fcntl(fd, F_GETFL, 0);
    if (flags < 0 || fcntl(fd, F_SETFL, flags | O_NONBLOCK) < 0) {
        perror("[SWIM-C] fcntl O_NONBLOCK");
        close(fd);
        return -1;
    }

    int reuse = 1;
    if (setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &reuse, sizeof(reuse)) < 0) {
        perror("[SWIM-C] setsockopt SO_REUSEADDR");
    }

    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_port = htons(port);
    if (bind_ip_str && strlen(bind_ip_str) > 0) {
        if (inet_pton(AF_INET, bind_ip_str, &addr.sin_addr) <= 0) {
            fprintf(stderr, "[SWIM-C] Invalid bind IP: %s\n", bind_ip_str);
            close(fd);
            return -1;
        }
    } else {
        addr.sin_addr.s_addr = htonl(INADDR_ANY);
    }

    if (bind(fd, (struct sockaddr*)&addr, sizeof(addr)) < 0) {
        perror("[SWIM-C] bind");
        close(fd);
        return -1;
    }

    return fd;
}

static bool parse_peer(const char* str, uint32_t* out_id, uint32_t* out_ip, uint16_t* out_port) {
    char ip_buf[64];
    unsigned int id_val = 0;
    unsigned int port_val = 0;
    if (sscanf(str, "%u:%63[^:]:%u", &id_val, ip_buf, &port_val) != 3) {
        return false;
    }
    struct in_addr in;
    if (inet_pton(AF_INET, ip_buf, &in) <= 0) {
        return false;
    }
    *out_id = (uint32_t)id_val;
    *out_ip = ntohl(in.s_addr);
    *out_port = (uint16_t)port_val;
    return true;
}

static lean_object* execute_actions_and_update(int sockfd, lean_object* step_result) {
    /* Unpack pair (NodeState × Array Action) */
    lean_object* new_state = lean_ctor_get(step_result, 0);
    lean_inc(new_state);
    lean_object* actions = lean_ctor_get(step_result, 1);
    lean_inc(actions);
    lean_dec(step_result);

    size_t num_actions = lean_array_size(actions);
    for (size_t i = 0; i < num_actions; i++) {
        /* act is borrowed from actions; increment refcount before owned @[export] calls */
        lean_object* act = lean_array_get_core(actions, i);

        lean_inc(act);
        if (swim_action_is_send(act)) {
            lean_inc(act);
            uint32_t dst_ip = swim_action_send_dest_ip(act);

            lean_inc(act);
            uint16_t dst_port = swim_action_send_dest_port(act);

            lean_inc(act);
            lean_object* payload_obj = swim_action_send_payload(act);

            size_t payload_len = lean_sarray_size(payload_obj);
            uint8_t* payload_data = lean_sarray_cptr(payload_obj);

            struct sockaddr_in dest_addr;
            memset(&dest_addr, 0, sizeof(dest_addr));
            dest_addr.sin_family = AF_INET;
            dest_addr.sin_port = htons(dst_port);
            dest_addr.sin_addr.s_addr = htonl(dst_ip);

            ssize_t sent = sendto(sockfd, payload_data, payload_len, 0,
                                  (struct sockaddr*)&dest_addr, sizeof(dest_addr));
            if (sent < 0) {
                if (errno != EAGAIN && errno != EWOULDBLOCK) {
                    perror("[SWIM-C] sendto error");
                }
            } else {
                char ip_buf[INET_ADDRSTRLEN];
                ip_to_str(dst_ip, ip_buf, sizeof(ip_buf));
                /* Debug trace */
                /* printf("[SWIM-C] Sent %zd bytes to %s:%u\n", sent, ip_buf, dst_port); */
            }

            lean_dec_ref(payload_obj);
        } else {
            lean_inc(act);
            if (swim_action_is_membership_change(act)) {
                lean_inc(act);
                uint32_t node = swim_action_membership_node(act);
                lean_inc(act);
                uint8_t status = swim_action_membership_status(act);
                lean_inc(act);
                uint32_t inc = swim_action_membership_incarnation(act);

                const char* status_str = (status == 0) ? "ALIVE" :
                                         (status == 1) ? "SUSPECT" :
                                         (status == 2) ? "DEAD" : "UNKNOWN";
                printf("[SWIM-C] Membership change: Node %u -> %s (incarnation %u)\n",
                       node, status_str, inc);
                fflush(stdout);
            }
        }
    }

    lean_dec(actions);
    return new_state;
}

static lean_object* handle_incoming_packets(int sockfd, lean_object* state) {
    uint8_t rx_buf[65536];

    while (1) {
        struct sockaddr_in src_addr;
        socklen_t addr_len = sizeof(src_addr);
        ssize_t n = recvfrom(sockfd, rx_buf, sizeof(rx_buf), 0,
                             (struct sockaddr*)&src_addr, &addr_len);
        if (n < 0) {
            if (errno == EAGAIN || errno == EWOULDBLOCK) {
                /* Sockets drained */
                break;
            }
            if (errno == EINTR) {
                continue;
            }
            perror("[SWIM-C] recvfrom error");
            break;
        }

        uint32_t src_ip = ntohl(src_addr.sin_addr.s_addr);
        uint16_t src_port = ntohs(src_addr.sin_port);
        uint64_t now_ms = get_monotonic_time_ms();

        /* Wrap buffer into Lean ByteArray */
        lean_object* payload_obj = lean_alloc_sarray(1, (size_t)n, (size_t)n);
        memcpy(lean_sarray_cptr(payload_obj), rx_buf, (size_t)n);

        /* Invoke pure state transition with received packet */
        lean_object* step_result = swim_step_packet(state, src_ip, src_port, payload_obj, now_ms);
        state = execute_actions_and_update(sockfd, step_result);
    }

    return state;
}

static lean_object* handle_timer_tick(int sockfd, lean_object* state, uint64_t now_ms) {
    lean_object* step_result = swim_step_tick(state, now_ms);
    return execute_actions_and_update(sockfd, step_result);
}

static void print_usage(const char* prog) {
    printf("Usage: %s [options]\n", prog);
    printf("Options:\n");
    printf("  -i, --id <node_id>       Local Node ID (default: 1)\n");
    printf("  -b, --bind <ip>          Bind IP address (default: 127.0.0.1)\n");
    printf("  -p, --port <port>        Bind UDP port (default: 9001)\n");
    printf("  -s, --seed <seed>        PRNG seed (default: random/time-based)\n");
    printf("  -t, --tick <interval_ms> Tick interval in milliseconds (default: 100)\n");
    printf("  -j, --peer <id:ip:port>  Seed peer to add (can be repeated)\n");
    printf("  -n, --ticks <count>      Run for N ticks and exit (default: run indefinitely)\n");
    printf("  -h, --help               Show this help message\n");
}

#define MAX_INITIAL_PEERS 64

struct PeerSpec {
    uint32_t id;
    uint32_t ip;
    uint16_t port;
};

int main(int argc, char* argv[]) {
    uint32_t node_id = 1;
    char bind_ip[64] = "127.0.0.1";
    uint16_t bind_port = 9001;
    uint64_t prng_seed = 0;
    bool seed_specified = false;
    uint32_t tick_interval_ms = 100;
    uint64_t max_ticks = 0;

    struct PeerSpec initial_peers[MAX_INITIAL_PEERS];
    size_t num_peers = 0;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-i") == 0 || strcmp(argv[i], "--id") == 0) {
            if (++i < argc) node_id = (uint32_t)strtoul(argv[i], NULL, 10);
        } else if (strcmp(argv[i], "-b") == 0 || strcmp(argv[i], "--bind") == 0) {
            if (++i < argc) strncpy(bind_ip, argv[i], sizeof(bind_ip) - 1);
        } else if (strcmp(argv[i], "-p") == 0 || strcmp(argv[i], "--port") == 0) {
            if (++i < argc) bind_port = (uint16_t)strtoul(argv[i], NULL, 10);
        } else if (strcmp(argv[i], "-s") == 0 || strcmp(argv[i], "--seed") == 0) {
            if (++i < argc) {
                prng_seed = (uint64_t)strtoull(argv[i], NULL, 10);
                seed_specified = true;
            }
        } else if (strcmp(argv[i], "-t") == 0 || strcmp(argv[i], "--tick") == 0) {
            if (++i < argc) tick_interval_ms = (uint32_t)strtoul(argv[i], NULL, 10);
        } else if (strcmp(argv[i], "-j") == 0 || strcmp(argv[i], "--peer") == 0) {
            if (++i < argc) {
                if (num_peers < MAX_INITIAL_PEERS) {
                    if (parse_peer(argv[i], &initial_peers[num_peers].id,
                                   &initial_peers[num_peers].ip,
                                   &initial_peers[num_peers].port)) {
                        num_peers++;
                    } else {
                        fprintf(stderr, "[SWIM-C] Invalid peer format: %s (expected id:ip:port)\n", argv[i]);
                    }
                }
            }
        } else if (strcmp(argv[i], "-n") == 0 || strcmp(argv[i], "--ticks") == 0) {
            if (++i < argc) max_ticks = (uint64_t)strtoull(argv[i], NULL, 10);
        } else if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
            print_usage(argv[0]);
            return 0;
        } else {
            fprintf(stderr, "[SWIM-C] Unknown argument: %s\n", argv[i]);
            print_usage(argv[0]);
            return 1;
        }
    }

    if (!seed_specified) {
        struct timespec ts;
        clock_gettime(CLOCK_REALTIME, &ts);
        prng_seed = ((uint64_t)ts.tv_sec ^ ((uint64_t)ts.tv_nsec << 16)) ^ (uint64_t)node_id;
    }

    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_handler = handle_signal;
    sigaction(SIGINT, &sa, NULL);
    sigaction(SIGTERM, &sa, NULL);

    /* 1. Initialize Lean 4 runtime */
    lean_initialize_runtime_module();
    lean_object* world = lean_io_mk_world();
    lean_object* init_res = initialize_SwimCore(1, world);
    if (lean_io_result_is_error(init_res)) {
        fprintf(stderr, "[SWIM-C] Fatal error initializing SwimCore module.\n");
        lean_dec_ref(init_res);
        return EXIT_FAILURE;
    }
    lean_dec_ref(init_res);

    /* 2. Bind POSIX non-blocking UDP socket */
    int sockfd = create_udp_socket(bind_ip, bind_port);
    if (sockfd < 0) {
        return EXIT_FAILURE;
    }

    struct in_addr bind_in;
    inet_pton(AF_INET, bind_ip, &bind_in);
    uint32_t bind_ip_int = ntohl(bind_in.s_addr);

    /* 3. Initialize SWIM node state */
    lean_object* state = swim_init_node(node_id, bind_ip_int, bind_port, prng_seed);

    /* Add initial cluster peers */
    for (size_t p = 0; p < num_peers; p++) {
        state = swim_add_peer(state, initial_peers[p].id, initial_peers[p].ip, initial_peers[p].port);
        char peer_ip_str[INET_ADDRSTRLEN];
        ip_to_str(initial_peers[p].ip, peer_ip_str, sizeof(peer_ip_str));
        printf("[SWIM-C] Added peer Node %u at %s:%u\n",
               initial_peers[p].id, peer_ip_str, initial_peers[p].port);
    }

    printf("[SWIM-C] Node %u initialized at %s:%u (seed: %llu, tick: %ums)\n",
           node_id, bind_ip, bind_port, (unsigned long long)prng_seed, tick_interval_ms);
    fflush(stdout);

    /* 4. Event Loop using poll */
    uint64_t next_tick_ms = get_monotonic_time_ms();
    uint64_t tick_count = 0;

    while (g_running) {
        uint64_t now_ms = get_monotonic_time_ms();
        lean_inc(state);
        uint64_t wakeup_ms = swim_next_wakeup_at(state);
        uint64_t due_ms = (wakeup_ms < next_tick_ms) ? wakeup_ms : next_tick_ms;

        /* Process timer tick when periodic tick or protocol deadline is reached */
        if (now_ms >= due_ms) {
            bool is_periodic = (now_ms >= next_tick_ms);
            state = handle_timer_tick(sockfd, state, now_ms);
            if (is_periodic) {
                tick_count++;
                if (max_ticks > 0 && tick_count >= max_ticks) {
                    printf("[SWIM-C] Reached max ticks (%llu), shutting down...\n",
                           (unsigned long long)max_ticks);
                    break;
                }
                next_tick_ms = now_ms + (uint64_t)tick_interval_ms;
            }
            now_ms = get_monotonic_time_ms();
            lean_inc(state);
            wakeup_ms = swim_next_wakeup_at(state);
            due_ms = (wakeup_ms < next_tick_ms) ? wakeup_ms : next_tick_ms;
        }

        /* Compute poll timeout in milliseconds using both periodic tick and Lean protocol deadline */
        int timeout_ms = 0;
        if (due_ms > now_ms) {
            uint64_t diff = due_ms - now_ms;
            timeout_ms = (diff > 1000ULL) ? 1000 : (int)diff;
        } else {
            timeout_ms = 1;
        }

        struct pollfd pfd;
        pfd.fd = sockfd;
        pfd.events = POLLIN;
        pfd.revents = 0;

        int ret = poll(&pfd, 1, timeout_ms);
        if (ret < 0) {
            if (errno == EINTR) {
                continue;
            }
            perror("[SWIM-C] poll error");
            break;
        }

        if (ret > 0 && (pfd.revents & POLLIN)) {
            state = handle_incoming_packets(sockfd, state);
        }
    }

    printf("[SWIM-C] Cleaning up and exiting...\n");
    lean_dec(state);
    close(sockfd);
    return EXIT_SUCCESS;
}
