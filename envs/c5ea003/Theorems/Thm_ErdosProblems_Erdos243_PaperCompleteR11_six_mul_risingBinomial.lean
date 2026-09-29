-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_six_mul_risingBinomial
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.six_mul_risingBinomial
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:49:29.426693+00:00
-- url     : https://prove2.me/theorems/3da94770-2201-4f56-bc3f-a83cfb81f1e2
-- title:
--   Lean source theorem: six_mul_risingBinomial
-- statement:
--   For every natural n, six times the integer rising binomial coefficient equals n(n+1)(n+2).
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicIntegralNormalisation.lean#L30-L35
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Mathlib
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Integral normalisation at the quarter-density threshold

The integral coefficients are
constructed from one clean four-window. In particular they are conclusions,
not hidden hypotheses in an arbitrary rational-profile statement.
- A non-integral constant or non-integral third difference gives density >= 1/4.
- The argument needs only an integer-valued sequence, not a recurrence.
- No claim that an integral constant must be +1 or -1 is made here.
-/

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.six_mul_risingBinomial (n : ℕ) :
    6 * risingBinomial n = (n : ℤ) * ((n : ℤ) + 1) * ((n : ℤ) + 2) := by sorry
