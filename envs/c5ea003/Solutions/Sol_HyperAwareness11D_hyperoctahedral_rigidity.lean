-- Prove2me | solution 1 for HyperAwareness11D.hyperoctahedral_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:24:33.750107+00:00
-- url     : https://prove2.me/submissions/2cc99aeb-dc5e-40a9-9596-33fa489e6fe5

-- Sol generated from MachineLearning/HyperAwareness11D/Equivariance.lean
import Mathlib
import Definitions.Def_MachineLearning_HyperAwareness11D_Equivariance
import Definitions.Def_MachineLearning_HyperAwareness11D_Injectivity
import Theorems.Thm_HyperAwareness11D_permEquivariant_iff_entries
import Theorems.Thm_HyperAwareness11D_permEquivariant_iff_invariant
import Theorems.Thm_HyperAwareness11D_signEquivariant_offDiag_zero

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
theorem solution(hn : 2 ≤ n) (M : Fin n → Fin n → ℝ) :
    (PermEquivariant M ∧ SignEquivariant M) ↔ ∃ a : ℝ, ∀ i j, M i j = if i = j then a else 0 := by
  classical
  have h0 : (0 : ℕ) < n := by omega
  have h1 : (1 : ℕ) < n := by omega
  set i0 : Fin n := ⟨0, h0⟩
  set i1 : Fin n := ⟨1, h1⟩
  have hi01 : i0 ≠ i1 := by
    intro hc
    have := congrArg Fin.val hc
    simp [i0, i1] at this
  constructor
  · rintro ⟨hp, hs⟩
    obtain ⟨a, b, hM⟩ := (permEquivariant_iff_entries hn M).mp hp
    have hb : b = 0 := by
      have h01 := hM i0 i1
      rw [if_neg hi01] at h01
      rw [← h01]
      exact signEquivariant_offDiag_zero M hs hi01
    exact ⟨a, by intro i j; rw [hM i j, hb]⟩
  · rintro ⟨a, hM⟩
    constructor
    · rw [permEquivariant_iff_invariant]
      intro σ i j
      by_cases hij : i = j
      · subst hij; simp [hM]
      · have : σ i ≠ σ j := fun hc => hij (σ.injective hc)
        simp [hM, hij, this]
    · intro ε hε x
      funext i
      simp only [linLayer, hM]
      rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
      · simp only [if_true]; ring
      · intro k _ hk; simp [Ne.symm hk]
      · intro hi; exact absurd (Finset.mem_univ i) hi
      · intro k _ hk; simp [Ne.symm hk]
      · intro hi; exact absurd (Finset.mem_univ i) hi
