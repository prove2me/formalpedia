-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubicQuotient_increment_eq
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.cubicQuotient_increment_eq
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:00:42.446073+00:00
-- url     : https://prove2.me/theorems/3ae8671e-10bc-4c9c-8706-7fd66e133a9e
-- title:
--   Lean source theorem: cubicQuotient_increment_eq
-- statement:
--   At every positive n with C(n) nonzero, the increment of the normalized quotient C(n)/[n(n+1)(n+2)] equals that quotient times the cubic ratio error, divided by 1+3/n.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateQuotientIncrement.lean#L15-L23
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Mathlib

/-!
# Erdős 243: quotient increments at the cubic rate
-/

noncomputable section


open Filter

open ErdosProblems.Erdos243.PaperCompleteR20

theorem ErdosProblems.Erdos243.PaperCompleteR20.cubicQuotient_increment_eq
    (C : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hC : C n ≠ 0) :
    cubicQuotient C (n + 1) - cubicQuotient C n =
      cubicQuotient C n * cubicRatioError C n /
        (1 + 3 / (n : ℝ)) := by sorry
