-- Prove2me | solution 1 for GodelCasinoAsymmetricOdds.expOdds_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:41:55.744892+00:00
-- url     : https://prove2.me/submissions/7e88919d-dd16-4dd3-b438-7e4bc00bde6a

-- Sol generated from Logic/GodelCasinoAsymmetricOdds.lean
import Mathlib
import Definitions.Def_Logic_GodelCasinoAsymmetricOdds
/-
# Gödel's Casino: asymmetric odds, transaction costs, and abstention

This file advances the randomized casino model from symmetric ±1 payoffs to
asymmetric odds.  A correct bet earns `a`, while an incorrect bet loses `b`.
The resulting break-even probability is `b / (a+b)` for betting true and
`a / (a+b)` for betting false.  We also add a zero-payoff abstention option.
-/

open GodelCasinoAsymmetricOdds

open Finset

variable {W : Type*} [Fintype W]



omit [Fintype W] in
/-- Closed form of the per-world randomized payoff. -/
lemma randOddsPayoff_eq (s : W → Bool) (a b r : ℚ) (ω : W) :
    randOddsPayoff s a b r ω =
      if s ω then (a + b) * r - b else a - (a + b) * r := by
  split_ifs with hs
  · unfold randOddsPayoff oddsPayoff; simp [hs]; ring
  · unfold randOddsPayoff oddsPayoff; simp [hs]; ring



















open GodelCasinoAsymmetricOdds in
theorem solution(μ : W → ℚ) (s : W → Bool) (a b r : ℚ) :
    expOdds μ s a b r =
      ((a + b) * r - b) * trueMass μ s +
      (a - (a + b) * r) * falseMass μ s := by
  simp only [expOdds, randOddsPayoff_eq, trueMass, falseMass]
  have h : ∀ ω, μ ω * (if s ω then (a + b) * r - b else a - (a + b) * r) =
           (if s ω then ((a + b) * r - b) * μ ω else (a - (a + b) * r) * μ ω) := fun ω => by
    split_ifs with hs <;> ring
  simp_rw [h]
  rw [Finset.sum_ite, Finset.sum_ite]
  congr 1
  · rw [← Finset.mul_sum]
    simp
  · rw [← Finset.mul_sum]
    apply congr_arg _
    rw [Finset.sum_ite]
    simp
