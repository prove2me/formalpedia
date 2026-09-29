-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_scale_twelve_of_square_in_adjoin
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.cubic_scale_twelve_of_square_in_adjoin
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:36:39.852674+00:00
-- url     : https://prove2.me/theorems/4e2d39ec-6442-4b82-864f-1840fb30b606
-- title:
--   Lean source theorem: cubic_scale_twelve_of_square_in_adjoin
-- statement:
--   Let m>0 and c=±1. If α is a root of the irreducible cubic X³−X+6c/m in a rational algebra field, and a β belonging to ℚ(α) satisfies β²=α²−1, then m=12.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicFieldScale.lean#L67-L80
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Mathlib
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.PowerBasis

   
                                                           

                                                                 
                                                                         
                                                                           
                                                                         
                                                                           
                                                                  
  


open Polynomial

noncomputable section

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.cubic_scale_twelve_of_square_in_adjoin
    {L : Type*} [Field L] [Algebra ℚ L]
    (m : ℕ) (c : ℚ) (hm : 0 < m) (hc : c = 1 ∨ c = -1)
    (α β : L)
    (hirr : Irreducible (cubicScalePolynomial (6*c/(m : ℚ))))
    (hroot : α^3 = α - algebraMap ℚ L (6*c/(m : ℚ)))
    (hβmem : β ∈ IntermediateField.adjoin ℚ ({α} : Set L))
    (hβ : β^2 = α^2 - 1) : m = 12 := by sorry
