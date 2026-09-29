-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
-- name    : ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T19:11:15.43351+00:00
-- url     : https://prove2.me/theorems/12a1461d-b3a9-4df0-a65e-d97aa8d58afa
-- title:
--   Rising binomial normalisation
-- statement:
--   Defines risingBinomial(n) as the integer binomial coefficient (n + 2 choose 3).
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicIntegralNormalisation.lean#L1-L142
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
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

namespace ErdosProblems.Erdos243.PaperCompleteR11

/-- Integer-valued binomial basis for a rising cubic. -/
def risingBinomial (n : ℕ) : ℤ := ((n + 2).choose 3 : ℤ)

















end ErdosProblems.Erdos243.PaperCompleteR11


