-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_rational_reciprocal_sum_cubic_rate_gives_positive_eventual_cubic
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.rational_reciprocal_sum_cubic_rate_gives_positive_eventual_cubic
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:51:37.991966+00:00
-- url     : https://prove2.me/theorems/f0cd30f3-0ea0-4131-9619-e6ea8fe83a5b
-- title:
--   Lean source theorem: rational_reciprocal_sum_cubic_rate_gives_positive_eventual_cubic
-- statement:
--   For a strictly increasing positive integer sequence with rational reciprocal sum p/q, if n³ times [(a(n)²/a(n+1))−(1+3/n)] tends to zero, then its canonical natural numerator eventually has a cubic profile A n(n+1)(n+2)+D with A,D rational and A>0.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateCanonicalBridge.lean#L142-L160
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientBounded
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Erdős 243: the rational reciprocal-tail cubic-rate bridge

This file returns from the paper's original sequence `a` to its canonical
positive integer tail numerator.  The quantitative tail comparison makes the
difference between the two consecutive ratios exponentially negligible, so
the literal `n^3`-scaled rate transfers without an extra hypothesis.
-/

noncomputable section


open Filter
open ErdosProblems.Erdos243.PaperCompleteR7

open ErdosProblems.Erdos243.PaperCompleteR20

theorem ErdosProblems.Erdos243.PaperCompleteR20.rational_reciprocal_sum_cubic_rate_gives_positive_eventual_cubic
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n : ℕ => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ))))
      atTop (nhds 0)) :
    ∃ A D : ℚ, 0 < A ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      (canonicalNaturalNumerator a p q n : ℝ) =
        (A : ℝ) * risingCubic n + (D : ℝ) := by sorry
