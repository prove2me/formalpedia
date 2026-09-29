-- Prove2me | solution 1 for HyperAwareness11D.exists_perm_pair
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:17:18.14114+00:00
-- url     : https://prove2.me/submissions/f0366c7f-a6e5-489d-990b-3e53d285a175

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
theorem solution{i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) :
    ∃ σ : Equiv.Perm (Fin n), σ i = k ∧ σ j = l := by
  classical
  set τ : Equiv.Perm (Fin n) := Equiv.swap i k with hτ
  have hτi : τ i = k := by simp [hτ]
  have hne : τ j ≠ k := by
    intro hjk
    have hji : τ j = τ i := by rw [hjk, hτi]
    exact hij (τ.injective hji).symm
  refine ⟨τ.trans (Equiv.swap (τ j) l), ?_, ?_⟩
  · simp only [Equiv.trans_apply, hτi]
    rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hne) hkl]
  · simp only [Equiv.trans_apply]
    rw [Equiv.swap_apply_left]
