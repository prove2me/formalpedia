-- Prove2me | solution 1 for PriceOfUniversality.exists_code_redundancy_le_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:05:24.052884+00:00
-- url     : https://prove2.me/submissions/e41a7d1b-37d1-45a2-a27b-3fa798d4773b

-- Sol generated from Novelty/UniversalRedundancyCore.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Theorems.Thm_PriceOfUniversality_IsPMF_le_one
import Theorems.Thm_PriceOfUniversality_shannonCode_isCode
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







open PriceOfUniversality in
theorem solution{p : A → ℝ} (hp : IsPMF p) (hpos : ∀ a, 0 < p a) :
    ∃ L : A → ℕ, IsCode L ∧ redundancy p L ≤ 1 := by
  refine ⟨shannonCode p, shannonCode_isCode hp hpos, ?_⟩
  have hlen : ∀ a : A, (shannonCode p a : ℝ) ≤ -logb 2 (p a) + 1 := by
    intro a
    have hnn : 0 ≤ -logb 2 (p a) := by
      have : logb 2 (p a) ≤ 0 := Real.logb_nonpos (by norm_num) (hpos a).le (hp.le_one a)
      linarith
    exact (Nat.ceil_lt_add_one hnn).le
  have hstep : expLen p (shannonCode p) ≤ ∑ a, p a * (-logb 2 (p a) + 1) := by
    refine Finset.sum_le_sum (fun a _ => ?_)
    exact mul_le_mul_of_nonneg_left (hlen a) (hp.nonneg a)
  have hsplit : ∑ a, p a * (-logb 2 (p a) + 1) = entropy p + 1 := by
    have hsp : ∑ a, p a * (-logb 2 (p a) + 1)
        = (∑ a, -(p a * logb 2 (p a))) + ∑ a, p a := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [hsp, hp.total, entropy]
  rw [redundancy]
  linarith [hstep, hsplit.le, hsplit.ge]
