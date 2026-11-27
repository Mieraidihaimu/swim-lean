#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

TMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/swim_exp.XXXXXX")"
PIDS=()
cleanup() {
    for pid in "${PIDS[@]:-}"; do
        kill -9 "$pid" 2>/dev/null || true
    done
    rm -rf "$TMP_DIR"
}
trap cleanup EXIT

echo "================================================================="
echo " SWIM-Lean: Proof -> Extracted C99 -> Load Generator Experiment"
echo "================================================================="
echo

# Stage 1: Direct Perceus FFI Stress + Runtime Refinement Safety Check
./loadgen --mode ffi --ops 200000 --peers 100
echo

# Stage 2: High-Rate Pipelined UDP Wire Load + Process RSS Observation
./swim_node --id 1 --port 19301 --tick 100 > "$TMP_DIR/udp_target.log" 2>&1 &
TARGET_PID=$!
PIDS+=("$TARGET_PID")
sleep 0.3

RSS_BEFORE_KB=$(ps -o rss= -p "$TARGET_PID" | tr -d ' ')
./loadgen --mode udp --ip 127.0.0.1 --port 19301 --ops 20000 --window 16 --fuzz-every 10
RSS_AFTER_KB=$(ps -o rss= -p "$TARGET_PID" | tr -d ' ')

kill -TERM "$TARGET_PID" 2>/dev/null || true
wait "$TARGET_PID" 2>/dev/null || true
echo "  Observed swim_node RSS: before=${RSS_BEFORE_KB} KiB -> after(20k reqs + 2k fuzz)=${RSS_AFTER_KB} KiB"
echo

# Stage 3: 5-Node Cluster Failure Detection Under Concurrent UDP Packet + Fuzz Storm
echo "=== [Experiment 3] 5-Node Cluster Churn Under Concurrent Load ==="
./swim_node --id 1 --port 19311 --tick 50 --peer 2:127.0.0.1:19312 --peer 3:127.0.0.1:19313 --peer 4:127.0.0.1:19314 --peer 5:127.0.0.1:19315 > "$TMP_DIR/n1.log" 2>&1 & P1=$!
./swim_node --id 2 --port 19312 --tick 50 --peer 1:127.0.0.1:19311 --peer 3:127.0.0.1:19313 --peer 4:127.0.0.1:19314 --peer 5:127.0.0.1:19315 > "$TMP_DIR/n2.log" 2>&1 & P2=$!
./swim_node --id 3 --port 19313 --tick 50 --peer 1:127.0.0.1:19311 --peer 2:127.0.0.1:19312 --peer 4:127.0.0.1:19314 --peer 5:127.0.0.1:19315 > "$TMP_DIR/n3.log" 2>&1 & P3=$!
./swim_node --id 4 --port 19314 --tick 50 --peer 1:127.0.0.1:19311 --peer 2:127.0.0.1:19312 --peer 3:127.0.0.1:19313 --peer 5:127.0.0.1:19315 > "$TMP_DIR/n4.log" 2>&1 & P4=$!
./swim_node --id 5 --port 19315 --tick 50 --peer 1:127.0.0.1:19311 --peer 2:127.0.0.1:19312 --peer 3:127.0.0.1:19313 --peer 4:127.0.0.1:19314 > "$TMP_DIR/n5.log" 2>&1 & P5=$!
PIDS+=("$P1" "$P2" "$P3" "$P4" "$P5")

sleep 0.5
./loadgen --mode storm --ip 127.0.0.1 --port 19311 --nodes 4 --duration-ms 6500 --pps 4000 &
STORM_PID=$!
PIDS+=("$STORM_PID")

sleep 0.8
echo "Injecting node crash: SIGKILL -> Node 5 (pid=$P5) while storming surviving Nodes 1..4..."
kill -9 "$P5" 2>/dev/null || true
wait "$P5" 2>/dev/null || true

wait "$STORM_PID"
kill -TERM "$P1" "$P2" "$P3" "$P4" 2>/dev/null || true
wait "$P1" "$P2" "$P3" "$P4" 2>/dev/null || true

DEAD_COUNT=0
for i in 1 2 3 4; do
    echo "  Node $i membership events:"
    grep "Membership change" "$TMP_DIR/n${i}.log" | sed 's/^/    /' || true
    if grep -q "Node 5 -> DEAD" "$TMP_DIR/n${i}.log"; then
        DEAD_COUNT=$((DEAD_COUNT + 1))
    fi
done

if [ "$DEAD_COUNT" -ne 4 ]; then
    echo "FAIL: Expected all 4 surviving nodes to converge on Node 5 -> DEAD under load (got $DEAD_COUNT/4)."
    exit 1
fi

echo
echo "SUCCESS: All 4 surviving nodes detected Node 5 SUSPECT -> DEAD under concurrent UDP load & fuzzing!"
