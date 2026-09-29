-- Prove2me | solution 1 for PriceOfUniversality.redundancy_eq_kl
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:37:39.069374+00:00
-- url     : https://prove2.me/submissions/4cbcbc6f-dcd4-4b54-9ac3-712a22b234bd

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







open PriceOfUniversality in
theorem solution{p : A → ℝ} (hp : IsPMF p) (L : A → ℕ) :
    redundancy p L = kl p (fun a => ((2:ℝ)⁻¹) ^ (L a)) := by
  rw [redundancy, expLen, entropy, kl, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro a _
  rcases eq_or_lt_of_le (hp.nonneg a) with h | h
  · simp [← h]
  · have hpow : (0:ℝ) < ((2:ℝ)⁻¹) ^ (L a) := by positivity
    have : logb 2 (p a / ((2:ℝ)⁻¹) ^ (L a)) = logb 2 (p a) + (L a : ℝ) := by
      rw [Real.logb_div (ne_of_gt h) (ne_of_gt hpow)]
      have hL2 : logb 2 (((2:ℝ)⁻¹) ^ (L a)) = -(L a : ℝ) := by
        rw [Real.logb_pow, Real.logb_inv]
        simp
      rw [hL2]; ring
    rw [this]; ring
