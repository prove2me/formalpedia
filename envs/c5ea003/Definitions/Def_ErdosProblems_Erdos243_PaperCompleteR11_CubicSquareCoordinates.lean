-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
-- name    : ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T18:52:38.539879+00:00
-- url     : https://prove2.me/theorems/33e7eb07-bbda-4936-8e9a-8091e034482d
-- title:
--   Rational coordinate expressions for the cubic exclusion
-- statement:
--   Defines the rational expressions cubicCoordinateB, cubicCoordinateD and cubicCoordinateW in the displayed coordinate variables.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicSquareCoordinates.lean#L1-L105
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Mathlib

   
                                           

                                                    

                                                                  
                                                                       
                                                                  
                                                                        
                                                                         
                                                                        
                                                                      

                                                             
                                                                       
                                                                   
  

namespace ErdosProblems.Erdos243.PaperCompleteR11

def cubicCoordinateB (x z : ℚ) : ℚ := -2*x-3*z

def cubicCoordinateD (x y z η : ℚ) : ℚ :=
  3*η*x*y + 3*η*x + x^2 + 4*x*z - y^2 - 2*y + 3*z^2 - 1

def cubicCoordinateW (x y z η : ℚ) : ℚ :=
  -η^2*x^3 - η*x^2*y - η*x^2 - 3*η*x*y*z - 3*η*x*z +
    η*y^3 + 3*η*y^2 + 3*η*y + η - x^2*z - 2*x*z^2 + y^2*z + 2*y*z - z^3 + z











end ErdosProblems.Erdos243.PaperCompleteR11


