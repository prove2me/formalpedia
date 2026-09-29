-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.cubic_scale_twelve_of_square_in_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:04:06.168515+00:00
-- url     : https://prove2.me/submissions/66b25abc-ef8c-4cd1-aff1-5123e4d7fd60

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_root_field_scale_twelve
import Mathlib
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.PowerBasis

   
                                                           

                                                                 
                                                                         
                                                                           
                                                                         
                                                                           
                                                                  
  

namespace ErdosProblems.Erdos243.PaperCompleteR11
open Polynomial

noncomputable section
end
end ErdosProblems.Erdos243.PaperCompleteR11

open Polynomial
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    {L : Type*} [Field L] [Algebra ℚ L]
    (m : ℕ) (c : ℚ) (hm : 0 < m) (hc : c = 1 ∨ c = -1)
    (α β : L)
    (hirr : Irreducible (cubicScalePolynomial (6*c/(m : ℚ))))
    (hroot : α^3 = α - algebraMap ℚ L (6*c/(m : ℚ)))
    (hβmem : β ∈ IntermediateField.adjoin ℚ ({α} : Set L))
    (hβ : β^2 = α^2 - 1) : m = 12 := by
  apply cubic_root_field_scale_twelve m c hm hc α hirr hroot
  refine ⟨⟨β, hβmem⟩, ?_⟩
  apply Subtype.ext
  simpa using hβ
