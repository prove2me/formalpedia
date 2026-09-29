-- Prove2me | solution 1 for FiniteAbelianUncertainty.donoho_stark_finite_abelian
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:39:35.366609+00:00
-- url     : https://prove2.me/submissions/18412311-24a5-4e8b-8358-0f8001eab7e2

-- Sol generated from Bridges/FiniteAbelianUncertainty.lean
import Mathlib
import Definitions.Def_Bridges_FiniteAbelianUncertainty
import Definitions.Def_Bridges_FourierFunctorUncertainty
import Theorems.Thm_FiniteAbelianUncertainty_gdft_inversion
import Theorems.Thm_FiniteAbelianUncertainty_mem_dsupport
import Theorems.Thm_FiniteAbelianUncertainty_mem_gsupport
import Theorems.Thm_FiniteAbelianUncertainty_norm_weighted_sum_le

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








omit [DecidableEq G] in
/-- Every Fourier coefficient is bounded by the support size times the sup norm. -/
theorem norm_gdft_le (f : G → ℂ) (M : ℝ) (hM : ∀ a, ‖f a‖ ≤ M) (psi : AddChar G ℂ) :
    ‖gdft f psi‖ ≤ (gsupport f).card * M := by
  classical
  refine norm_weighted_sum_le (fun a => psi (-a)) f M (fun a => le_of_eq
    (AddChar.norm_apply _ _)) hM (gsupport f) ?_
  intro a ha
  by_contra h
  exact ha (mem_gsupport.2 h)


/-! ## Sharpness -/







open FiniteAbelianUncertainty in
theorem solution(f : G → ℂ) (hf : f ≠ 0) :
    Fintype.card G ≤ (gsupport f).card * (dsupport (gdft f)).card := by
  classical
  obtain ⟨a₀⟩ : Nonempty G := ⟨0⟩
  obtain ⟨b, -, hb⟩ :=
    Finset.exists_max_image (Finset.univ : Finset G) (fun a => ‖f a‖) ⟨a₀, mem_univ _⟩
  set M : ℝ := ‖f b‖ with hMdef
  have hM : ∀ a, ‖f a‖ ≤ M := fun a => hb a (mem_univ a)
  have hMpos : 0 < M := by
    rcases lt_or_eq_of_le (norm_nonneg (f b)) with h | h
    · exact h
    · exfalso
      apply hf
      funext a
      have : ‖f a‖ ≤ 0 := by rw [hMdef, ← h] at hM; exact hM a
      simpa using le_antisymm this (norm_nonneg _)
  have h1 : ∀ psi : AddChar G ℂ, ‖gdft f psi‖ ≤ (gsupport f).card * M := norm_gdft_le f M hM
  have h2 : ‖∑ psi : AddChar G ℂ, psi b * gdft f psi‖
      ≤ (dsupport (gdft f)).card * ((gsupport f).card * M) := by
    refine norm_weighted_sum_le (fun psi => psi b) (gdft f) _
      (fun psi => le_of_eq (AddChar.norm_apply _ _)) h1 (dsupport (gdft f)) ?_
    intro psi hpsi
    by_contra h
    exact hpsi (mem_dsupport.2 h)
  rw [gdft_inversion f b, norm_mul] at h2
  have h3 : (Fintype.card G : ℝ) * M
      ≤ (dsupport (gdft f)).card * ((gsupport f).card * M) := by
    simpa using h2
  have h4 : (Fintype.card G : ℝ) * M
      ≤ ((gsupport f).card * (dsupport (gdft f)).card : ℝ) * M := by nlinarith [h3]
  exact_mod_cast le_of_mul_le_mul_right h4 hMpos
