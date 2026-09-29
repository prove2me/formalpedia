-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.cubicScalePolynomial_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:48:43.036976+00:00
-- url     : https://prove2.me/submissions/a51100c9-1082-414f-93b8-6fcd21474b70

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

namespace ErdosProblems.Erdos243.PaperCompleteR11
open Polynomial
open scoped BigOperators

noncomputable section
end
end ErdosProblems.Erdos243.PaperCompleteR11

open Polynomial
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution (η : ℚ) :
    (cubicScalePolynomial η).natDegree = 3 := by
  dsimp [cubicScalePolynomial]
  compute_degree
  exact one_ne_zero
