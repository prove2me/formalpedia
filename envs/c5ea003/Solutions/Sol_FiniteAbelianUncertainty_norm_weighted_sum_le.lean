-- Prove2me | solution 1 for FiniteAbelianUncertainty.norm_weighted_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:36:52.614649+00:00
-- url     : https://prove2.me/submissions/4c15fac8-33c3-4fe5-9c50-0644beb42d70

-- Sol generated from Bridges/FiniteAbelianUncertainty.lean
import Mathlib
import Definitions.Def_Bridges_FiniteAbelianUncertainty
import Definitions.Def_Bridges_FourierFunctorUncertainty

/-!
# Donoho–Stark uncertainty for arbitrary finite abelian groups

`Catalog/Bridges/FourierFunctorUncertainty.lean` proved the Donoho–Stark uncertainty principle on
`ZMod N`, where the characters are explicit roots of unity. This file shows the argument is
structural rather than cyclic: it needs only that characters have modulus one and that the
character-sum inversion formula holds. We therefore obtain the uncertainty principle for an
arbitrary finite abelian group `G`, with the Fourier transform taking values on the Pontryagin
dual `AddChar G ℂ`.

## Main results

* `FiniteAbelianUncertainty.gdft_inversion` : the character-sum inversion formula
  `∑_ψ ψ b · 𝓖f(ψ) = |G| · f b`.
* `FiniteAbelianUncertainty.donoho_stark_finite_abelian` : for every nonzero `f : G → ℂ`,
  `|G| ≤ |supp f| * |supp 𝓖f|`, the support on the right being taken in the dual group.
* `FiniteAbelianUncertainty.donoho_stark_sharp_delta` : the bound is attained by delta functions,
  so it is sharp for every finite abelian group.
-/

open Finset AddChar

open FiniteAbelianUncertainty

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]










/-! ## Sharpness -/







open FiniteAbelianUncertainty in
theorem solution{I : Type*} [Fintype I] (w g : I → ℂ) (K : ℝ)
    (hw : ∀ i, ‖w i‖ ≤ 1) (hK : ∀ i, ‖g i‖ ≤ K) (S : Finset I) (hS : ∀ i, i ∉ S → g i = 0) :
    ‖∑ i, w i * g i‖ ≤ S.card * K := by
  classical
  have hsum : ∑ i, w i * g i = ∑ i ∈ S, w i * g i := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro x _ hx
    simp [hS x hx]
  rw [hsum]
  calc ‖∑ i ∈ S, w i * g i‖
      ≤ ∑ i ∈ S, ‖w i * g i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ S, K := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul]
        exact le_trans (mul_le_mul (hw i) (hK i) (norm_nonneg _) zero_le_one)
          (le_of_eq (one_mul K))
    _ = S.card * K := by rw [Finset.sum_const, nsmul_eq_mul]
