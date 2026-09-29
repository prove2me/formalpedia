-- Prove2me | solution 1 for Rademacher.signAvg_le_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:56:30.626168+00:00
-- url     : https://prove2.me/submissions/e5f57cc2-61ec-4a4e-8c65-005e1c17a072

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



lemma abs_sgn (ε : Fin n → Bool) (i : Fin n) : |sgn ε i| = 1 := by
  simp only [sgn]; cases ε i <;> simp

















open Rademacher in
theorem solution{v : Fin n → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ i, |v i| ≤ B) (ε : Fin n → Bool) : signAvg ε v ≤ B := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [signAvg, hB]
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hterm : ∀ i : Fin n, sgn ε i * v i ≤ B := by
    intro i
    calc sgn ε i * v i ≤ |sgn ε i * v i| := le_abs_self _
      _ = |sgn ε i| * |v i| := abs_mul _ _
      _ = |v i| := by rw [abs_sgn]; ring
      _ ≤ B := hv i
  have : ∑ i, sgn ε i * v i ≤ (n : ℝ) * B := by
    calc ∑ i, sgn ε i * v i ≤ ∑ _i : Fin n, B := Finset.sum_le_sum fun i _ => hterm i
      _ = (n : ℝ) * B := by simp [Finset.sum_const, mul_comm]
  unfold signAvg
  rw [one_div, inv_mul_le_iff₀ hn']
  linarith
