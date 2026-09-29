-- Prove2me | solution 1 for PriceOfUniversality.shannonCode_isCode
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:03:10.222846+00:00
-- url     : https://prove2.me/submissions/0bc07431-d8ce-445f-9397-1d9b7d0000b9

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

    

/-! ## Source coding lower bound -/




/-! ## The Shannon code: the per-source optimum costs at most one extra bit -/



private lemma two_inv_pow_eq_rpow (k : ℕ) : ((2:ℝ)⁻¹) ^ k = (2:ℝ) ^ (-(k : ℝ)) := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]




open PriceOfUniversality in
theorem solution{p : A → ℝ} (hp : IsPMF p) (hpos : ∀ a, 0 < p a) :
    IsCode (shannonCode p) := by
  have hle : ∀ a : A, ((2:ℝ)⁻¹) ^ (shannonCode p a) ≤ p a := by
    intro a
    rw [two_inv_pow_eq_rpow]
    have hceil : -logb 2 (p a) ≤ (⌈-logb 2 (p a)⌉₊ : ℝ) := Nat.le_ceil _
    have hexp : -((shannonCode p a : ℝ)) ≤ logb 2 (p a) := by
      simp only [shannonCode]; linarith
    calc (2:ℝ) ^ (-(shannonCode p a : ℝ))
        ≤ (2:ℝ) ^ (logb 2 (p a)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = p a := Real.rpow_logb (by norm_num) (by norm_num) (hpos a)
  calc kraftSum (shannonCode p) ≤ ∑ a, p a := Finset.sum_le_sum (fun a _ => hle a)
    _ = 1 := hp.total
