# SWIM-Lean: Verified SWIM Gossip Failure Detector in Lean 4

A formally verified, high-performance implementation of the **SWIM (Structured Weakly-Consistent Infection-Style Process Group Membership Protocol)** Gossip Failure Detector in **Lean 4**, combining:
- Strict **Sans-IO** separation between pure deterministic protocol transitions and POSIX I/O.
- **Axiom-free Mathlib4 formalization** of Phase 1 (exponential growth from $1 \to n/2$ via Chernoff bounds and stochastic dominance) and Phase 2 (exponential tail collapse $n/2 \to n$) establishing $O(\log n)$ w.h.p. epidemic dissemination.
- **Universal binary wire bijection** (`decodeMessage (encodeMessage msg) = some msg` for all well-formed messages) and **state-machine safety refinement** linking `SwimCore.step` directly to the join-semilattice `Dominates` monotonicity invariant.
- Extraction to in-place mutating C99 code via Lean 4 Perceus IR (`lean --c`) with protocol-deadline-aware `poll` wakeups and deterministic simulation testing (DST).

## Architecture

- **`SwimCore/`**: Zero-dependency executable state machine (`UInt32`, `UInt64`, `ByteArray`, `Array`):
  - `Types.lean`, `Prng.lean` (`SplitMix64`), `Wire.lean` (compact big-endian binary codec), `Dissemination.lean` ($\lceil \log_2 n \rceil$-bounded gossip piggybacking), `FailureDetector.lean` (`stepTick`, `stepRecvPacket` with transitive `pendingRelays` for `pingReq`, saturating self-refutation, tail-recursive `checkSuspectTimeoutsLoop`, and `nextWakeupAt`), `Exports.lean` (`@[export]` C ABI).
- **`SwimProofs/`**: Zero-dependency Lean 4 core safety, wire, and refinement proofs:
  - `Safety.lean`: Join-semilattice `Dominates` relation and total/transitive ordering over `(incarnation, status)`.
  - `WireProofs.lean`: Universal roundtrip theorem `decodeMessage_encodeMessage_wellFormed`.
  - `Refinement.lean`: State-machine safety theorem `step_preserves_safety` proving every `Event.tick` and `Event.recvPacket` preserves `StateMonotonic`.
  - `EpidemicModel.lean` / `Convergence.lean`: Lightweight standalone model (axiomatized `Real` for fast dependency-free CI).
- **`SwimMathlib/`**: Isolated `Mathlib4` (`v4.36.0`) proof package importing `SwimCore`:
  - `SwimMathlibProofs/EpidemicPMF.lean`: Exact `PMF` push-gossip Markov chain & Phase 2 convergence (`phase2_convergence_whp`), **0 axioms, 0 `sorry`s**.
  - `SwimMathlibProofs/Phase1Growth.lean`: Coupled `Binomial(m, 1/2)` exponential MGF Chernoff bound & full $1 \to n$ Phase 1 + Phase 2 theorem (`full_epidemic_convergence_whp`), **0 axioms, 0 `sorry`s**.
- **`SimMain.lean`**: `SplitMix64` deterministic discrete-event simulation testing (DST) suite verifying 0 false positives, crash dissemination, asymmetric indirect `pingReq` relay recovery, 10% packet loss tolerance, and empirical $O(\log n)$ scaling up to $N = 64$.
- **`c_runtime/`**: C99 POSIX UDP harness linking `libswim_SwimCore.a` + `libleanshared` with `swim_next_wakeup_at` deadline scheduling.

## Quick Start

```bash
# Build SwimCore, SwimProofs, and the deterministic simulator
lake build && lake build swim_sim
.lake/build/bin/swim_sim

# Build the axiom-free Mathlib4 epidemic proofs (uses Mathlib cache)
cd SwimMathlib && lake exe cache get && lake build SwimMathlibProofs && cd ..

# Compile C runtime, run the smoke test, and run the load-generator experiment
make -C c_runtime && make -C c_runtime test
make -C c_runtime loadtest
```

## Proof -> Extracted C -> Load-Generator Experiment

[`c_runtime/loadgen.c`](c_runtime/loadgen.c) and [`c_runtime/run_experiment.sh`](c_runtime/run_experiment.sh) stress-test the compiled Lean-4 Perceus C artifact (`libswim_SwimCore.a` + `swim_node`) across three automated stages:

1. **Direct Perceus FFI Stress (`--mode ffi`)**: Executes 200,000 mixed state transitions (70% valid SWIM packets with piggybacked gossip & self-suspicion refutation, 25% malformed/fuzzed wire payloads, 5% timer ticks) on a 100-peer node while runtime-checking `Refinement.step_preserves_safety` invariants (`members_size` constant, `incarnation` monotonic) on every step (~1.81M transitions/sec, `p99 = 2us`, `max = 19us`).
2. **Live UDP Wire Load (`--mode udp`)**: Drives 20,000 pipelined UDP `Ping -> Ack` roundtrips plus 2,000 malformed UDP frames against a live `swim_node` process (~116.6k roundtrips/sec, `p50 = 77us`, `p99 = 236us`, 0.000% loss, `swim_node` RSS unchanged at 10,768 KiB).
3. **Cluster Churn Under Concurrent Load (`--mode storm`)**: Blasts a live 5-node `swim_node` UDP cluster with ~4,000 pps + 10% malformed fuzz packets while injecting `SIGKILL` on Node 5, verifying all 4 surviving processes converge on `Node 5 -> SUSPECT -> DEAD`.
