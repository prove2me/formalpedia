-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_Limits
-- name    : ErdosProblems_Erdos243_PaperCompleteR7_Limits
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:28:33.60411+00:00
-- url     : https://prove2.me/theorems/fca1f751-92d0-4f34-90c8-af84000b7723
-- title:
--   Natural absolute-value and ratio bridges
-- statement:
--   Contains proved coercion and limit equivalences connecting natural absolute values, real ratios, and division-free normalized vanishing. It introduces no new rigidity conclusion.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/PaperCompleteR7/Limits.lean#L1-L130
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_PaperCompleteR7_Limits is the versioned native alias of original module ErdosProblems.Erdos243.PaperCompleteR7.Limits.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring

/-!
# Real limits and the division-free hypotheses used by the corpus

Compiled candidates.  In particular, the real limit in the sparse-gcd
paper statement is not silently replaced by an assumed arithmetic bound.
The equivalence is proved here.  Little-o of the count relative to N is
expressed as convergence of count/N to zero (the denominator is eventually
positive).
-/

namespace ErdosProblems.Erdos243.PaperCompleteR7

open Filter

/-- Cast conversion used to align the printed absolute value with the
integer magnitude in the existing declarations. -/
theorem natAbs_cast_real (z : ℤ) : (Int.natAbs z : ℝ) = |(z : ℝ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]

/-- A real ratio tending to zero is exactly the division-free natural
form used in `ReciprocalTailRigidity`.  Positivity is only eventual. -/
theorem nat_ratio_tendsto_zero_iff
    (m d : ℕ → ℕ)
    (hd : ∃ N, ∀ n, N ≤ n → 0 < d n) :
    Tendsto (fun n ↦ (m n : ℝ) / (d n : ℝ)) atTop (nhds 0) ↔
      ∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * m n < d n := by
  obtain ⟨Nd, hNd⟩ := hd
  constructor
  · intro hlim K
    have heps : (0 : ℝ) < 1 / ((K : ℝ) + 1) := by positivity
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim _ heps
    refine ⟨max Nd N, fun n hn ↦ ?_⟩
    have hdn : (0 : ℝ) < d n := by
      exact_mod_cast hNd n ((Nat.le_max_left Nd N).trans hn)
    have hnonneg : (0 : ℝ) ≤ (m n : ℝ) / (d n : ℝ) := by positivity
    have hlt : (m n : ℝ) / (d n : ℝ) < 1 / ((K : ℝ) + 1) := by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using
        hN n ((Nat.le_max_right Nd N).trans hn)
    have hm : (m n : ℝ) * ((K : ℝ) + 1) < (d n : ℝ) := by
      have hmul := (div_lt_div_iff₀ hdn (by positivity : (0 : ℝ) < K + 1)).mp hlt
      simpa only [one_mul] using hmul
    have hk : (K : ℝ) * (m n : ℝ) < (d n : ℝ) := by
      nlinarith [show (0 : ℝ) ≤ (m n : ℝ) by positivity]
    exact_mod_cast hk
  · intro hsmall
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε)
    have hKpos : (0 : ℝ) < K := (one_div_pos.mpr hε).trans hK
    have hrecip : (1 : ℝ) / K < ε := by
      apply (div_lt_iff₀ hKpos).mpr
      have hprod := (div_lt_iff₀ hε).mp hK
      nlinarith
    obtain ⟨N, hN⟩ := hsmall K
    refine ⟨max Nd N, fun n hn ↦ ?_⟩
    have hdn : (0 : ℝ) < d n := by
      exact_mod_cast hNd n ((Nat.le_max_left Nd N).trans hn)
    have hmul : (m n : ℝ) * (K : ℝ) < (d n : ℝ) := by
      have hk : K * m n < d n := hN n ((Nat.le_max_right Nd N).trans hn)
      exact_mod_cast (by simpa only [Nat.mul_comm] using hk : m n * K < d n)
    have hlt : (m n : ℝ) / (d n : ℝ) < 1 / (K : ℝ) := by
      apply (div_lt_div_iff₀ hdn hKpos).mpr
      simpa only [one_mul] using hmul
    have hnonneg : (0 : ℝ) ≤ (m n : ℝ) / (d n : ℝ) := by positivity
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using
      hlt.trans hrecip

/-- Printed real normalised vanishing and the exact arithmetic interface. -/
theorem normalized_vanishing_iff
    (C : ℕ → ℕ) (E : ℕ → ℤ) (hCpos : ∀ n, 0 < C n) :
    Tendsto (fun n ↦ |(E n : ℝ)| / (C n : ℝ)) atTop (nhds 0) ↔
      ∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n := by
  have h := nat_ratio_tendsto_zero_iff (fun n ↦ Int.natAbs (E n)) C
    ⟨0, fun n _ ↦ hCpos n⟩
  simpa only [natAbs_cast_real] using h





end ErdosProblems.Erdos243.PaperCompleteR7


