-- Prove2me | solution 1 for FiniteAbelianUncertainty.gdft_inversion
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:36:57.227982+00:00
-- url     : https://prove2.me/submissions/4f98659c-1ba1-4bb0-882b-34bb8ec7dbbb

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
theorem solution(f : G → ℂ) (b : G) :
    ∑ psi : AddChar G ℂ, psi b * gdft f psi = (Fintype.card G : ℂ) * f b := by
  classical
  simp only [gdft, Finset.mul_sum]
  rw [Finset.sum_comm]
  have key : ∀ a : G, ∑ psi : AddChar G ℂ, psi b * (psi (-a) * f a)
      = (if b - a = 0 then (Fintype.card G : ℂ) else 0) * f a := by
    intro a
    rw [← AddChar.sum_apply_eq_ite (b - a), Finset.sum_mul]
    refine Finset.sum_congr rfl fun psi _ => ?_
    rw [← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    abel
  rw [Finset.sum_congr rfl fun a _ => key a, Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    have : b - c ≠ 0 := sub_ne_zero.2 (Ne.symm hc)
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ b) h
