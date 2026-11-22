# SWIM-Lean: Verified SWIM Gossip Failure Detector in Lean 4

A formally verified, high-performance implementation of the **SWIM (Structured Weakly-Consistent Infection-Style Process Group Membership Protocol)** Gossip Failure Detector in **Lean 4**, with:
- Strict **Sans-IO** separation between pure deterministic protocol transitions and POSIX I/O.
- Bounded $\mathcal{O}(\log n)$ epidemic dissemination and convergence analysis.
- Extraction to zero-pause, in-place mutating C code via Lean 4 IR (`lean --c`).
- POSIX UDP runtime harness (`kqueue` / `epoll`).

## Architecture

- **`SwimCore`**: Zero-dependency executable state machine. Pure transitions on `UInt32`, `UInt64`, `ByteArray`, and `Array`.
- **`SwimProofs`**: Formal verification using Mathlib4 (discrete PMF Markov chains, Chernoff bounds, two-phase Pittel/Karp analysis, and simulation refinement).
- **`c_runtime`**: C99 imperative shell hosting the Lean runtime and running the non-blocking UDP event loop.

## Quick Start

```bash
# Build the Lean core & Lake targets
lake build

# Compile C code and run the UDP failure detector node
make -C c_runtime
```
