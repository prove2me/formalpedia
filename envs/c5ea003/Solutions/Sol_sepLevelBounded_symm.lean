-- Prove2me | solution 1 for sepLevelBounded_symm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:24:20.04118+00:00
-- url     : https://prove2.me/submissions/e77a27e0-7eab-4c8a-9b5b-cbc0d63de46c

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















theorem solution{P ι S : Type*} [DecidableEq S] [Fintype ι]
    (O : ι → P → S) (lvl : ι → ℕ) (x y : P) :
    sepLevelBounded O lvl x y = sepLevelBounded O lvl y x := by
  simp only [sepLevelBounded]
  have key : (∃ i : ι, O i x ≠ O i y) ↔ (∃ i : ι, O i y ≠ O i x) := by
    constructor <;> exact fun ⟨i, hi⟩ => ⟨i, hi ∘ Eq.symm⟩
  by_cases h : ∃ i : ι, O i x ≠ O i y
  · simp only [dif_pos h, dif_pos (key.mp h)]
    congr 1
    ext v
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi ∘ Eq.symm, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi ∘ Eq.symm, rfl⟩
  · have hrev : ¬∃ i, O i y ≠ O i x := fun ⟨i, hi⟩ => h ⟨i, hi ∘ Eq.symm⟩
    simp only [dif_neg h, dif_neg hrev]
