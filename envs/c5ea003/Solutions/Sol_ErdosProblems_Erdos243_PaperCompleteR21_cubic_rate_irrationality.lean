-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR21.cubic_rate_irrationality
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:37:54.432154+00:00
-- url     : https://prove2.me/submissions/65725ef0-7941-4cbe-90c1-f7b4da813e97

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicQuarticWindows
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicQuarticCertificates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicZeroDensityShape
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientBounded
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR21_CubicRateExclusionChain
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_canonical_integer_tail
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_rational_reciprocal_sum_cubic_rate_gives_positive_eventual_cubic
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR21_cubic_exclusion
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Erdős 243: from the square specialisation to cubic-rate irrationality

Development file: the three paper environments downstream of
`long243:res:squarespec`, proved from that lemma taken as the hypothesis
`SquareSpecialisation`.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR21
open ErdosProblems.Erdos243.PaperCompleteR7
open ErdosProblems.Erdos243.PaperCompleteR9
open ErdosProblems.Erdos243.PaperCompleteR11
open ErdosProblems.Erdos243.PaperCompleteR20





/-! ### `long243:res:transportsquare` -/





/-! ### `long243:res:cubicexclusion` -/



/-! ### `res:cubicrate` and `long243:res:cubicrate` -/
end ErdosProblems.Erdos243.PaperCompleteR21

open ErdosProblems.Erdos243.PaperCompleteR7
open ErdosProblems.Erdos243.PaperCompleteR9
open ErdosProblems.Erdos243.PaperCompleteR11
open ErdosProblems.Erdos243.PaperCompleteR20
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR21 in
set_option maxHeartbeats 1000000 in

theorem solution (hss : SquareSpecialisation)
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hrate : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ))))
      Filter.atTop (nhds 0))
    (Sv : ℝ) (hS : HasSum (fun n : ℕ => 1 / (a n : ℝ)) Sv) :
    Irrational Sv := by
  rintro ⟨q, hq⟩
  have hS' : HasSum (fun n : ℕ => 1 / (a n : ℝ)) ((q.num : ℝ) / (q.den : ℝ)) := by
    rw [show ((q.num : ℝ) / (q.den : ℝ)) = (q : ℝ) from (Rat.cast_def q).symm, hq]
    exact hS
  obtain ⟨Ac, Dc, hAc, N, hN⟩ :=
    rational_reciprocal_sum_cubic_rate_gives_positive_eventual_cubic a ha hpos
      q.num q.den q.pos hS' hrate
  obtain ⟨hCpos, hDpos, hCrec, hDrec, -⟩ :=
    canonical_integer_tail a hpos q.num q.den q.pos hS'
  have hapos : ∀ n : ℕ, 0 < ((a n : ℤ)) := by
    intro n
    exact_mod_cast hpos n
  have hCpos' : ∀ n : ℕ, 0 < ((canonicalNaturalNumerator a q.num q.den n : ℤ)) := by
    intro n
    exact_mod_cast hCpos n
  have hDpos' : ∀ n : ℕ, 0 < ((canonicalDenominator a q.den n : ℤ)) := by
    intro n
    exact_mod_cast hDpos n
  have hCrec' : ∀ n : ℕ,
      ((canonicalNaturalNumerator a q.num q.den (n + 1) : ℤ))
        = ((a n : ℤ)) * ((canonicalNaturalNumerator a q.num q.den n : ℤ))
          - ((canonicalDenominator a q.den n : ℤ)) := by
    intro n
    have h : ((canonicalNaturalNumerator a q.num q.den (n + 1)
        + canonicalDenominator a q.den n : ℕ) : ℤ)
        = ((a n * canonicalNaturalNumerator a q.num q.den n : ℕ) : ℤ) := by
      exact_mod_cast hCrec n
    push_cast at h
    linarith
  have hDrec' : ∀ n : ℕ,
      ((canonicalDenominator a q.den (n + 1) : ℤ))
        = ((a n : ℤ)) * ((canonicalDenominator a q.den n : ℤ)) := by
    intro n
    have h : ((canonicalDenominator a q.den (n + 1) : ℕ) : ℤ)
        = ((a n * canonicalDenominator a q.den n : ℕ) : ℤ) := by
      exact_mod_cast hDrec n
    push_cast at h
    linarith
  refine (cubic_exclusion hss (fun n => (a n : ℤ))
      (fun n => (canonicalNaturalNumerator a q.num q.den n : ℤ))
      (fun n => (canonicalDenominator a q.den n : ℤ))
      hapos hCpos' hDpos' hCrec' hDrec' Ac Dc hAc).2 ⟨N, ?_⟩
  intro n hn
  have h := hN n hn
  simp only [risingCubic] at h
  have hQ : (((canonicalNaturalNumerator a q.num q.den n : ℕ) : ℚ) : ℝ)
      = ((Ac * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + Dc : ℚ) : ℝ) := by
    push_cast
    push_cast at h
    linarith
  have hq2 : ((canonicalNaturalNumerator a q.num q.den n : ℕ) : ℚ)
      = Ac * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + Dc := by
    exact_mod_cast hQ
  exact_mod_cast hq2
