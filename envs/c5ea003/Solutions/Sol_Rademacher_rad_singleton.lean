-- Prove2me | solution 1 for Rademacher.rad_singleton
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:56:29.981878+00:00
-- url     : https://prove2.me/submissions/3375942a-1a18-4448-8ce5-5abf68fc41bc

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

lemma sum_sgn_eq_zero (i : Fin n) : ∑ ε : Fin n → Bool, sgn ε i = 0 := by
  have h := sum_sign_neg (fun ε => sgn ε i)
  simp only [sgn_neg] at h
  rw [Finset.sum_neg_distrib] at h
  linarith

lemma signAvg_singleton (ε : Fin n → Bool) (v : Fin n → ℝ) :
    sSup (signAvg ε '' ({v} : Set (Fin n → ℝ))) = signAvg ε v := by
  simp [Set.image_singleton]










open Rademacher in
theorem solution(v : Fin n → ℝ) : rad ({v} : Set (Fin n → ℝ)) = 0 := by
  unfold rad
  rw [Finset.sum_congr rfl (fun ε _ => signAvg_singleton ε v)]
  have : ∑ ε : Fin n → Bool, signAvg ε v = 0 := by
    unfold signAvg
    rw [← Finset.mul_sum, Finset.sum_comm]
    have : ∀ i : Fin n, ∑ ε : Fin n → Bool, sgn ε i * v i = 0 := by
      intro i
      rw [← Finset.sum_mul, sum_sgn_eq_zero i, zero_mul]
    simp [this]
  rw [this]
  simp
