/--
  Pure deterministic pseudo-random number generator (SplitMix64)
  and random permutation / sampling routines for SWIM.
-/

@[inline]
def _root_.Array.swap! [Inhabited α] (arr : Array α) (i j : Nat) : Array α :=
  if h : i < arr.size ∧ j < arr.size then
    arr.swap i j h.1 h.2
  else
    arr

namespace SwimCore.Prng

/-- Pure 64-bit SplitMix64 pseudo-random generator step.
    Advances state `s` and returns `(randomValue, nextState)`. -/
@[inline]
def splitMix64Next (s : UInt64) : UInt64 × UInt64 :=
  let s' := s + 0x9e3779b97f4a7c15
  let z0 := s'
  let z1 := (z0 ^^^ (z0 >>> 30)) * 0xbf58476d1ce4e5b9
  let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94d049bb133111eb
  let res := z2 ^^^ (z2 >>> 31)
  (res, s')

/-- Generates a pseudo-random 32-bit unsigned integer uniformly distributed in `[min, max]` (inclusive).
    Returns `(value, nextState)`. -/
def randomRange (s : UInt64) (min max : UInt32) : UInt32 × UInt64 :=
  let (sVal, s') := splitMix64Next s
  if min == max then
    (min, s')
  else
    let (lo, hi) := if min < max then (min, max) else (max, min)
    let span : UInt64 := (hi.toUInt64 - lo.toUInt64 + 1)
    let offset : UInt32 := (sVal % span).toUInt32
    (lo + offset, s')

/-- In-place Fisher-Yates shuffle of an array using `arr.swap!`.
    Returns `(shuffledArray, nextState)`. -/
def shuffleArray [Inhabited α] (arr : Array α) (s : UInt64) : Array α × UInt64 :=
  if arr.size <= 1 then
    (arr, s)
  else
    Id.run do
      let mut a := arr
      let mut st := s
      for i in [0:a.size - 1] do
        let (j32, nextSt) := randomRange st i.toUInt32 (a.size - 1).toUInt32
        let j := j32.toNat
        a := a.swap! i j
        st := nextSt
      return (a, st)

/-- Randomly selects `k` distinct elements from `arr` (clamped to `arr.size`)
    using a partial in-place Fisher-Yates shuffle.
    Returns `(sampledArray, nextState)`. -/
def pickKRandom [Inhabited α] (arr : Array α) (k : Nat) (s : UInt64) : Array α × UInt64 :=
  if k == 0 || arr.isEmpty then
    (#[], s)
  else
    let count := min k arr.size
    Id.run do
      let mut a := arr
      let mut st := s
      for i in [0:count] do
        let (j32, nextSt) := randomRange st i.toUInt32 (a.size - 1).toUInt32
        let j := j32.toNat
        a := a.swap! i j
        st := nextSt
      return (a.extract 0 count, st)

end SwimCore.Prng

namespace SwimCore
export Prng (splitMix64Next randomRange shuffleArray pickKRandom)
end SwimCore
