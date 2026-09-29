-- Prove2me | solution 1 for HyperAwareness11D.signEquivariant_offDiag_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:23:08.317951+00:00
-- url     : https://prove2.me/submissions/1894b38a-741e-4a91-9124-49e5f4fe42a8

-- Sol generated from MachineLearning/HyperAwareness11D/Equivariance.lean
import Mathlib
import Definitions.Def_MachineLearning_HyperAwareness11D_Equivariance
import Definitions.Def_MachineLearning_HyperAwareness11D_Injectivity

/-!
# Hyper-Awareness III: symmetry rigidity of 11-dimensional perception layers

A recurring design proposal for "hyper-aware" architectures is to make the 11 spatial axes
*interchangeable*, i.e. to impose the symmetries of the 11-dimensional hypercube on every
linear layer.  This file proves that such a demand is self-defeating, by computing exactly
which linear layers `x ↦ M x` on `ℝ¹¹` are equivariant for the two natural symmetry groups:

* the symmetric group `S₁₁` (permuting the 11 axes), and
* the hyperoctahedral group `B₁₁ = (ℤ/2)¹¹ ⋊ S₁₁` (permuting *and* reflecting the axes).

## Main results

* `HyperAwareness11D.permEquivariant_iff_entries` — permutation equivariance is exactly the
  statement that `M` has constant diagonal and constant off-diagonal entries.
* `HyperAwareness11D.permEquivariant_deepSets` — hence such a layer has the "Deep Sets" form
  `x ↦ a • x + b • (∑ x)`: **exactly two learnable parameters**, versus `121` for a general
  `11 × 11` layer.
* `HyperAwareness11D.exists_unique_deepSets_params` — the two parameters are unique.
* `HyperAwareness11D.signEquivariant_offDiag_zero` — sign equivariance forces `M` diagonal.
* `HyperAwareness11D.hyperoctahedral_rigidity` — the two symmetries together force
  `M = a • 1`: **exactly one learnable parameter**, a global gain.
* `HyperAwareness11D.no_hyperoctahedral_channel_swap` — consequently no `B₁₁`-equivariant
  layer can mix two perception channels: hypercube symmetry annihilates all
  11-dimensional cross-channel processing.

The moral for the mission: *lossless* 11-dimensional processing (the `22`-unit optimum of
`Injectivity.lean`) and *fully symmetric* 11-dimensional processing are incompatible design
goals; genuine 11-dimensional perception must break the hyperoctahedral symmetry.
-/

open HyperAwareness11D

open Finset

noncomputable section

variable {n : ℕ}




/-! ## A two-point transitivity lemma for permutations -/


/-! ## Permutation equivariance -/





/-! ## Sign equivariance and hyperoctahedral rigidity -/







open HyperAwareness11D in
theorem solution(M : Fin n → Fin n → ℝ) (h : SignEquivariant M)
    {i j : Fin n} (hij : i ≠ j) : M i j = 0 := by
  classical
  set ε : Fin n → ℝ := fun k => if k = j then -1 else 1 with hε
  have hεspec : ∀ k, ε k = 1 ∨ ε k = -1 := by
    intro k; by_cases hk : k = j <;> simp [hε, hk]
  set x : Fin n → ℝ := fun k => if k = j then (1:ℝ) else 0 with hx
  have hcall := congrFun (h ε hεspec x) i
  simp only [linLayer] at hcall
  have hL : (∑ k, M i k * (ε k * x k)) = -M i j := by
    rw [Finset.sum_eq_single j]
    · simp [hε, hx]
    · intro k _ hk; simp [hx, hk]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  have hR : (∑ k, M i k * x k) = M i j := by
    rw [Finset.sum_eq_single j]
    · simp [hx]
    · intro k _ hk; simp [hx, hk]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [hL, hR] at hcall
  have hεi : ε i = 1 := by simp [hε, hij]
  rw [hεi] at hcall
  linarith [hcall]
