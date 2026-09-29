-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.cubic_root_field_scale_twelve
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:01:11.793534+00:00
-- url     : https://prove2.me/submissions/69d922f3-a185-4a0e-b99f-4abb8069dbc4

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubicScalePolynomial_natDegree
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubicScalePolynomial_monic
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_powerBasis_square_parameter
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_scale_rational_classification
import Mathlib
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.PowerBasis

   
                                                           

                                                                 
                                                                         
                                                                           
                                                                         
                                                                           
                                                                  
  

namespace ErdosProblems.Erdos243.PaperCompleteR11
open Polynomial

noncomputable section

/-- A three-dimensional power basis is enough to compose the complete
algebraic scale argument. -/
theorem cubic_powerBasis_scale_twelve
    {K : Type*} [CommRing K] [Nontrivial K] [Algebra ℚ K]
    (pb : PowerBasis ℚ K) (hdim : pb.dim = 3)
    (m : ℕ) (c : ℚ) (hm : 0 < m) (hc : c = 1 ∨ c = -1)
    (hroot : pb.gen^3 = pb.gen - algebraMap ℚ K (6*c/(m : ℚ)))
    (hsquare : ∃ β : K, β^2 = pb.gen^2 - 1) : m = 12 := by
  obtain ⟨w, hw, heq⟩ := cubic_powerBasis_square_parameter pb hdim
    (6*c/(m : ℚ)) hroot hsquare
  exact cubic_scale_rational_classification m c w hm hc hw heq
end
end ErdosProblems.Erdos243.PaperCompleteR11

open Polynomial
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    {L : Type*} [Field L] [Algebra ℚ L]
    (m : ℕ) (c : ℚ) (hm : 0 < m) (hc : c = 1 ∨ c = -1)
    (α : L)
    (hirr : Irreducible (cubicScalePolynomial (6*c/(m : ℚ))))
    (hroot : α^3 = α - algebraMap ℚ L (6*c/(m : ℚ)))
    (hsquare : ∃ β : IntermediateField.adjoin ℚ ({α} : Set L),
      β^2 = (IntermediateField.AdjoinSimple.gen ℚ α)^2 - 1) : m = 12 := by
  let η : ℚ := 6*c/(m : ℚ)
  have heval : aeval α (cubicScalePolynomial η) = 0 := by
    simp only [cubicScalePolynomial, map_add, map_sub, map_pow,
      Polynomial.aeval_X, Polynomial.aeval_C]
    dsimp [η]
    linear_combination hroot
  have hint : IsIntegral ℚ α :=
    ⟨cubicScalePolynomial η, cubicScalePolynomial_monic η, heval⟩
  have hmin : cubicScalePolynomial η = minpoly ℚ α :=
    minpoly.eq_of_irreducible_of_monic hirr heval (cubicScalePolynomial_monic η)
  letI : Algebra ℚ (IntermediateField.adjoin ℚ ({α} : Set L)) :=
    (IntermediateField.adjoin ℚ ({α} : Set L)).algebra'
  let pb := IntermediateField.adjoin.powerBasis hint
  have hdim : pb.dim = 3 := by
    change (minpoly ℚ α).natDegree = 3
    rw [← hmin, cubicScalePolynomial_natDegree]
  have hgen : pb.gen^3 = pb.gen -
      algebraMap ℚ (IntermediateField.adjoin ℚ ({α} : Set L)) η := by
    apply Subtype.ext
    change α^3 = α - algebraMap ℚ L η
    exact hroot
  exact cubic_powerBasis_scale_twelve pb hdim m c hm hc hgen hsquare
