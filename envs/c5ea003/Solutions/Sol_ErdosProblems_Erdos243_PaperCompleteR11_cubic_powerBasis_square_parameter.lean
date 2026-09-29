-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.cubic_powerBasis_square_parameter
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:51:03.136457+00:00
-- url     : https://prove2.me/submissions/ec1b80f7-dcb4-4a43-be19-4ba9a84d27bb

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_coordinate_parameter_ne_zero
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_coordinate_scale_relations
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_powerBasis_square_coordinates
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
theorem solution
    {K : Type*} [CommRing K] [Nontrivial K] [Algebra ℚ K]
    (pb : PowerBasis ℚ K) (hdim : pb.dim = 3) (η : ℚ)
    (hroot : pb.gen^3 = pb.gen - algebraMap ℚ K η)
    (hsquare : ∃ β : K, β^2 = pb.gen^2 - 1) :
    ∃ w : ℚ, w ≠ 0 ∧
      ((w^2 + 1)^2 = 8*η*w^3 ∨ (w^2 + 1)^2 = 8*η*w) := by
  obtain ⟨β, hβ⟩ := hsquare
  obtain ⟨x, y, z, _, h1, h2, h3⟩ :=
    cubic_powerBasis_square_coordinates pb hdim η hroot β hβ
  exact ⟨cubicCoordinateW x y z η,
    cubic_coordinate_parameter_ne_zero x y z η h1 h2 h3,
    cubic_coordinate_scale_relations x y z η h1 h2 h3⟩
