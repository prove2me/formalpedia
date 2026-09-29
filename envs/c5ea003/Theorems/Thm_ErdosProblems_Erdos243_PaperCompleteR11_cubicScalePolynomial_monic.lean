-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubicScalePolynomial_monic
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.cubicScalePolynomial_monic
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T21:00:06.718758+00:00
-- url     : https://prove2.me/theorems/3e5ea1df-455e-4844-83e8-9c671430b082
-- title:
--   Monicity of the cubic scale polynomial
-- statement:
--   For every rational parameter η, cubicScalePolynomial(η) is monic.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicFieldCoordinates.lean#L27-L31
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Mathlib
import Mathlib.RingTheory.PowerBasis

/-!
# Extracting the square-root coordinates from a cubic algebra

The power-basis representation is extracted from the actual square root.
The degree bound then forces all three rational coordinate equations.
No trace, norm, coordinate equation, or coefficient relation is assumed.
-/


open Polynomial
open scoped BigOperators

noncomputable section

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.cubicScalePolynomial_monic (η : ℚ) :
    (cubicScalePolynomial η).Monic := by sorry
