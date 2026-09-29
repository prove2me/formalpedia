-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
-- name    : ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T18:57:08.444991+00:00
-- url     : https://prove2.me/theorems/12e91663-61f2-49dc-99fe-98d0e7794f02
-- title:
--   Cubic scale polynomial
-- statement:
--   Defines the rational polynomial X³ − X + η, parametrised by η.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicFieldCoordinates.lean#L1-L112
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Mathlib
import Mathlib.RingTheory.PowerBasis

/-!
# Extracting the square-root coordinates from a cubic algebra

The power-basis representation is extracted from the actual square root.
The degree bound then forces all three rational coordinate equations.
No trace, norm, coordinate equation, or coefficient relation is assumed.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open Polynomial
open scoped BigOperators

noncomputable section

def cubicScalePolynomial (η : ℚ) : ℚ[X] := X^3 - X + C η











end

end ErdosProblems.Erdos243.PaperCompleteR11


