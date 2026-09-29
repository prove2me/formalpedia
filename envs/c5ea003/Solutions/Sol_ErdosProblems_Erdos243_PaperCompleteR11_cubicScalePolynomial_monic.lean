-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.cubicScalePolynomial_monic
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:21:36.058135+00:00
-- url     : https://prove2.me/submissions/d9bb1de5-e0b6-4615-8482-cb0ae815b9c0

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubicScalePolynomial_natDegree
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
    (cubicScalePolynomial η).Monic := by
  change (cubicScalePolynomial η).coeff (cubicScalePolynomial η).natDegree = 1
  rw [cubicScalePolynomial_natDegree]
  norm_num [cubicScalePolynomial, Polynomial.coeff_X]
