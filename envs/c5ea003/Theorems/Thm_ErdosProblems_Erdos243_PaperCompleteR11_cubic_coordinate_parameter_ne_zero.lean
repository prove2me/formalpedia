-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_coordinate_parameter_ne_zero
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.cubic_coordinate_parameter_ne_zero
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:25:03.283852+00:00
-- url     : https://prove2.me/theorems/d77254bd-d0c8-4c78-a09b-28fcd5eac96f
-- title:
--   Lean source theorem: cubic_coordinate_parameter_ne_zero
-- statement:
--   For rational x,y,z,η satisfying x²+2xz+y²−1=0, 2xy+2yz−ηx²=0 and z²−2ηxy+1=0, the defined rational coordinate W(x,y,z,η) is nonzero.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicSquareCoordinates.lean#L71-L85
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Mathlib

   
                                           

                                                    

                                                                  
                                                                       
                                                                  
                                                                        
                                                                         
                                                                        
                                                                      

                                                             
                                                                       
                                                                   
  

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.cubic_coordinate_parameter_ne_zero
    (x y z η : ℚ)
    (h1 : x^2 + 2*x*z + y^2 - 1 = 0)
    (h2 : 2*x*y + 2*y*z - η*x^2 = 0)
    (h3 : z^2 - 2*η*x*y + 1 = 0) : cubicCoordinateW x y z η ≠ 0 := by sorry
