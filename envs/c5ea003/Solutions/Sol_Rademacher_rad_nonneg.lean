-- Prove2me | solution 1 for Rademacher.rad_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:56:29.421725+00:00
-- url     : https://prove2.me/submissions/205a7f91-c989-40ce-bc01-c96164aa6ead

-- Sol generated from Logic/Rademacher/Basic.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Basic
/-
# Empirical Rademacher complexity: definitions and basic calculus

This file sets up the *empirical Rademacher complexity* of a class of real vectors
indexed by a finite sample of size `n`.  If `F : Set (Fin n → ℝ)` is the restriction
of a hypothesis class to a sample `x₁, …, xₙ`, its empirical Rademacher complexity is

  `R(F) = 𝔼_σ [ sup_{v ∈ F} (1/n) ∑ i, σ i * v i ]`,

where `σ` ranges uniformly over the `2ⁿ` sign vectors in `{-1, 1}ⁿ`.
The expectation is realised as an explicit finite average over `Fin n → Bool`.

The basic calculus proved here: the complexity of a singleton vanishes, it is
monotone in the class, nonnegative for nonempty classes, homogeneous under scaling,
invariant under translation, and bounded by any uniform bound on the coordinates.
-/

open Rademacher

open Finset

variable {n : ℕ}


@[simp] lemma sgn_neg (ε : Fin n → Bool) (i : Fin n) :
    sgn (fun j => !(ε j)) i = -sgn ε i := by
  simp only [sgn]
  rcases Bool.eq_false_or_eq_true (ε i) with h | h <;> simp [h]






/-- Flipping all signs is an involution of the sign vectors, so a sum over sign
vectors is unchanged by negating the signs. -/
lemma sum_sign_neg (g : (Fin n → Bool) → ℝ) :
    ∑ ε : Fin n → Bool, g (fun j => !(ε j)) = ∑ ε : Fin n → Bool, g ε := by
  refine Finset.sum_nbij' (fun ε => fun j => !(ε j)) (fun ε => fun j => !(ε j))
    ?_ ?_ ?_ ?_ ?_ <;> intros <;> simp












open Rademacher in
theorem solution{F : Set (Fin n → ℝ)} (hF : F.Nonempty)
    (hb : ∀ ε : Fin n → Bool, BddAbove (signAvg ε '' F)) :
    0 ≤ rad F := by
  obtain ⟨v, hv⟩ := hF
  have key : ∀ ε : Fin n → Bool,
      0 ≤ sSup (signAvg ε '' F) + sSup (signAvg (fun j => !(ε j)) '' F) := by
    intro ε
    have h1 : signAvg ε v ≤ sSup (signAvg ε '' F) :=
      le_csSup (hb ε) ⟨v, hv, rfl⟩
    have h2 : signAvg (fun j => !(ε j)) v ≤ sSup (signAvg (fun j => !(ε j)) '' F) :=
      le_csSup (hb _) ⟨v, hv, rfl⟩
    have h3 : signAvg (fun j => !(ε j)) v = -signAvg ε v := by
      unfold signAvg
      simp [sgn_neg, Finset.sum_neg_distrib, mul_neg, neg_mul]
    rw [h3] at h2
    linarith
  have hsum : 0 ≤ ∑ ε : Fin n → Bool, sSup (signAvg ε '' F) := by
    have hneg : ∑ ε : Fin n → Bool, sSup (signAvg (fun j => !(ε j)) '' F)
        = ∑ ε : Fin n → Bool, sSup (signAvg ε '' F) :=
      sum_sign_neg (fun ε => sSup (signAvg ε '' F))
    have := Finset.sum_le_sum (fun ε (_ : ε ∈ (Finset.univ : Finset (Fin n → Bool))) =>
      key ε)
    simp only [Finset.sum_const, smul_zero, Finset.sum_add_distrib] at this
    rw [hneg] at this
    linarith
  unfold rad
  have hpow : (0:ℝ) < 2 ^ n := by positivity
  exact div_nonneg hsum hpow.le
