-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_powerBasis_square_coordinates
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.cubic_powerBasis_square_coordinates
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:31:58.406114+00:00
-- url     : https://prove2.me/theorems/c8b64a75-bc61-494c-97ea-59635756a176
-- title:
--   Lean source theorem: cubic_powerBasis_square_coordinates
-- statement:
--   In a nontrivial commutative rational algebra with a three-dimensional power basis whose generator α satisfies α³=α−η, any β with β²=α²−1 has rational coordinates β=xα²+yα+z satisfying all three displayed square-root coordinate equations.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicFieldCoordinates.lean#L48-L87
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

theorem ErdosProblems.Erdos243.PaperCompleteR11.cubic_powerBasis_square_coordinates
    {K : Type*} [CommRing K] [Nontrivial K] [Algebra ℚ K]
    (pb : PowerBasis ℚ K) (hdim : pb.dim = 3) (η : ℚ)
    (hroot : pb.gen^3 = pb.gen - algebraMap ℚ K η)
    (β : K) (hsquare : β^2 = pb.gen^2 - 1) :
    ∃ x y z : ℚ,
      β = algebraMap ℚ K x * pb.gen^2 + algebraMap ℚ K y * pb.gen +
        algebraMap ℚ K z ∧
      x^2 + 2*x*z + y^2 - 1 = 0 ∧
      2*x*y + 2*y*z - η*x^2 = 0 ∧
      z^2 - 2*η*x*y + 1 = 0 := by sorry
