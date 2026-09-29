-- Prove2me | solution 1 for NatUltrametric.ball_center_shift
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:14:22.538273+00:00
-- url     : https://prove2.me/submissions/2d136224-adca-46e5-93fc-f9ef0638ef26

-- Sol generated from Bridges/UltrametricProofCodeDuality.lean
import Mathlib
import Definitions.Def_Bridges_UltrametricProofCodeDuality
/-
# Ultrametric Proof-Code Duality

This file establishes a formal algebraic dictionary between three domains:
1. **Prime-congruence algebra** on finite observer families
2. **Finite ultrametric geometry** and dendrogram reconstruction
3. **Certified hierarchical decoding** with cryptographic semantics

## Main Results

### Core Definitions
* `kernelAtLevel` — equivalence relation induced by observers up to a given level
* `NatUltrametric` — ℕ-valued ultrametric structure
* `ObsKernel` — kernel of a subfamily of observers
* `NestedPartitionSystem` — certified hierarchical partition
* `sepLevelBounded` — separation level between points

### Theorems
* `kernelAtLevel_refl/symm/trans` — observer kernels are equivalence relations
* `kernelAtLevel_antitone` — higher levels yield finer kernels
* `closedBall_eq_kernelClass` — closed balls are exactly observer kernel classes
* `ultrametric_isosceles` — all ultrametric triangles are isosceles
* `canonical_observers_separate` — canonical observers separate points
* `canonical_full_separation` — full characterization of separation
* `reconstruction_correct` — round-trip correctness
* `sepLevelBounded_ultrametric` — separation levels satisfy ultrametric inequality
* `binaryTree_*` — concrete verified example on a 4-point ultrametric
-/


set_option maxHeartbeats 800000

open Finset Function

noncomputable section

/-! ## §1. Observer Kernels and Level Filtrations -/



/-! ## §2. Kernel Equivalence Relations -/






/-! ## §3. ℕ-Valued Ultrametric -/



/-! ## §4. Closed Balls -/




/-! ## §5. Ball-Kernel Duality -/


/-! ## §6. Ultrametric Isosceles Theorem -/

/-
**Ultrametric isosceles theorem**: In any `NatUltrametric`, if `d(x,y) ≠ d(y,z)`,
    then `d(x,z) = max(d(x,y), d(y,z))`.
-/

/-! ## §7. Observer Kernel Lattice -/




/-! ## §8. Nested Partition Systems and Reconstruction -/




/-! ## §9. Canonical Observers and Separation -/





/-! ## §10. Decoding Duality -/


/-! ## §11. Kernel Refinement Chain -/


/-! ## §12. Separation Level and Ultrametric Inequality -/




/-
Helper: sepLevelBounded is ≤ lvl j for any distinguishing observer j.
-/





/-
Helper: obsDist is ≥ lvl j for any distinguishing observer j.
-/

/-
**Ultrametric inequality for observer distance**:
    `obsDist(x,z) ≤ max(obsDist(x,y), obsDist(y,z))`.

    Any observer distinguishing `x` from `z` must also distinguish either
    `x` from `y` or `y` from `z`, so its level contributes to one of the
    right-hand side maxima.
-/

/-! ## §13. Concrete Example: Binary Tree Ultrametric -/















theorem solution{P : Type*} (U : NatUltrametric P)
    (x y : P) (k : ℕ) (hxy : U.d x y ≤ k) :
    U.closedBall x k = U.closedBall y k := by
  ext z
  simp only [NatUltrametric.closedBall, Set.mem_setOf_eq]
  constructor
  · intro hxz
    calc U.d y z ≤ max (U.d y x) (U.d x z) := U.d_ultra y x z
    _ = max (U.d x y) (U.d x z) := by rw [U.d_symm y x]
    _ ≤ max k k := max_le_max hxy hxz
    _ = k := max_self k
  · intro hyz
    calc U.d x z ≤ max (U.d x y) (U.d y z) := U.d_ultra x y z
    _ ≤ max k k := max_le_max hxy hyz
    _ = k := max_self k
