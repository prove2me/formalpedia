-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_coordinate_scale_relations
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.cubic_coordinate_scale_relations
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:25:16.927009+00:00
-- url     : https://prove2.me/theorems/e23adce8-b8b0-495e-99f5-3fd5b88a0783
-- title:
--   Lean source theorem: cubic_coordinate_scale_relations
-- statement:
--   For rational x,y,z,η satisfying x²+2xz+y²−1=0, 2xy+2yz−ηx²=0 and z²−2ηxy+1=0, the defined coordinate W satisfies (W²+1)²=8ηW³ or (W²+1)²=8ηW.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicSquareCoordinates.lean#L87-L103
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Mathlib

   
                                           

                                                    

                                                                  
                                                                       
                                                                  
                                                                        
                                                                         
                                                                        
                                                                      

                                                             
                                                                       
                                                                   
  

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.cubic_coordinate_scale_relations
    (x y z η : ℚ)
    (h1 : x^2 + 2*x*z + y^2 - 1 = 0)
    (h2 : 2*x*y + 2*y*z - η*x^2 = 0)
    (h3 : z^2 - 2*η*x*y + 1 = 0) :
    let w := cubicCoordinateW x y z η
    (w^2 + 1)^2 = 8*η*w^3 ∨ (w^2 + 1)^2 = 8*η*w := by sorry
