-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubicQuotient_eventually_bounded_of_ratio_error
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.cubicQuotient_eventually_bounded_of_ratio_error
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:32:47.850727+00:00
-- url     : https://prove2.me/theorems/69f18736-489e-4725-ae15-5446a8785af0
-- title:
--   Lean source theorem: cubicQuotient_eventually_bounded_of_ratio_error
-- statement:
--   For an eventually nonzero real sequence whose error from the cubic model ratio 1+3/n is o(n⁻³), the normalized quotient C(n)/[n(n+1)(n+2)] is eventually bounded in absolute value.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateQuotientBounded.lean#L69-L110
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
import Mathlib
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Erdős 243: boundedness of the cubic quotient

The literal `o(n⁻³)` relative error is summable.  Iterating the exact quotient
recurrence therefore expresses the quotient as a fixed initial value times a
convergent infinite-product prefix, which is eventually bounded.
-/

noncomputable section


open Filter Finset

open ErdosProblems.Erdos243.PaperCompleteR20

theorem ErdosProblems.Erdos243.PaperCompleteR20.cubicQuotient_eventually_bounded_of_ratio_error
    (C : ℕ → ℝ)
    (hC : ∀ᶠ n in atTop, C n ≠ 0)
    (hratio : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 * cubicRatioError C n) atTop (nhds 0)) :
    ∃ M : ℝ, ∀ᶠ n in atTop, |cubicQuotient C n| ≤ M := by sorry
