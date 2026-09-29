-- Prove2me | solution 1 for PriceOfUniversality.kl_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:37:38.15033+00:00
-- url     : https://prove2.me/submissions/0626394e-ce0a-46fc-aafe-3497abbbce42

-- Sol generated from Novelty/UniversalRedundancyCore.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
/-
# The price of universality, I: codes, entropy and per-source redundancy

This file sets up the basic apparatus used throughout the *price of universality*
development:

* length functions and the Kraft inequality (`IsCode`),
* Shannon entropy, relative entropy (Kullback-Leibler divergence) and
  expected code length, all measured in **bits**,
* Gibbs' inequality (`kl_nonneg`),
* the source coding lower bound `entropy_le_expLen`, i.e. *redundancy is
  nonnegative*, and
* the Shannon code, showing the per-source optimum is within one bit of the
  entropy (`exists_code_redundancy_le_one`).

Everything is finitary and completely self-contained.
-/

open PriceOfUniversality

open Finset Real

variable {A : Type*} [Fintype A]

/-! ## Codes -/




/-! ## Information quantities (in bits) -/





/-! ## Gibbs' inequality -/

private lemma log_ratio_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) :
    x * Real.log (y / x) ≤ y - x := by
  rcases eq_or_lt_of_le hx with h | hx'
  · simp [← h, hy.le]
  · have h1 : Real.log (y / x) ≤ y / x - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have := mul_le_mul_of_nonneg_left h1 hx
    calc x * Real.log (y / x) ≤ x * (y / x - 1) := this
      _ = y - x := by field_simp
    

/-! ## Source coding lower bound -/




/-! ## The Shannon code: the per-source optimum costs at most one extra bit -/







open PriceOfUniversality in
theorem solution{p q : A → ℝ} (hp : IsPMF p) (hq : ∀ a, 0 < q a)
    (hq1 : ∑ a, q a ≤ 1) : 0 ≤ kl p q := by
  have key : ∑ a, p a * Real.log (q a / p a) ≤ 0 := by
    have h1 : ∀ a ∈ (univ : Finset A), p a * Real.log (q a / p a) ≤ q a - p a := by
      intro a _
      exact log_ratio_le _ _ (hp.nonneg a) (hq a)
    calc ∑ a, p a * Real.log (q a / p a) ≤ ∑ a, (q a - p a) := Finset.sum_le_sum h1
      _ = (∑ a, q a) - 1 := by rw [Finset.sum_sub_distrib, hp.total]
      _ ≤ 0 := by linarith
  have hswap : ∀ a, p a * logb 2 (p a / q a) = -((p a * Real.log (q a / p a)) / Real.log 2) := by
    intro a
    rcases eq_or_lt_of_le (hp.nonneg a) with h | h
    · simp [← h]
    · have : p a / q a = (q a / p a)⁻¹ := by
        field_simp
      rw [logb, this, Real.log_inv]
      ring
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [kl]
  simp only [hswap, ← neg_div]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]
  exact div_nonneg (by linarith) h2.le
