-- Prove2me | Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
-- name    : ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T18:39:28.385303+00:00
-- url     : https://prove2.me/theorems/b46f88e2-3642-4967-b174-ca2d4f5c0de1
-- title:
--   Scalar power and geometric-series bounds
-- statement:
--   For real 0 < t and 0 < α ≤ 1, t^(−α) ≤ max(1, t⁻¹). For real B > 1, the infinite sum Σ_{r≥0}(B^(r+1))⁻¹ equals 1/(B−1).
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR7/CoverKernel.lean#L1-L373
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

   
                                                             

                                                                             
                                                                             
                                                                            

                                                                                
                                                                                
                            
                                                                                        
                                                           
                                                                                
                                                                   

                                                                            
                                                                          
                                                            
                                                                             
                                                  
                                                                           
                                                                             
                                                                              
                                                                              
                                                                                
                                                              

                                                                               
                                                                              
                                                                                
                                                                    
                                                           
  

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR7

open Finset Filter





/-- The scalar tail-budget bound `ε ^ (-α) ≤ max 1 ε⁻¹`, uniform over the
exponents `0 < α ≤ 1`. -/
theorem rpow_neg_le_max_one_inv {t α : ℝ} (ht : 0 < t) (hα : 0 < α) (hα1 : α ≤ 1) :
    t ^ (-α) ≤ max 1 t⁻¹ := by
  rcases le_total t 1 with h | h
  · have hmono : t ^ (-α) ≤ t ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ht h (by linarith)
    rw [Real.rpow_neg_one] at hmono
    exact hmono.trans (le_max_right _ _)
  · have hone : t ^ (-α) ≤ t ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h (by linarith)
    rw [Real.rpow_zero] at hone
    exact hone.trans (le_max_left _ _)

/-- The geometric factor of the displayed cost condition. -/
theorem tsum_inv_pow_succ {B : ℝ} (hB : 1 < B) :
    ∑' r : ℕ, (B ^ (r + 1))⁻¹ = 1 / (B - 1) := by
  have hB0 : (0 : ℝ) < B := lt_trans zero_lt_one hB
  have hBne : B ≠ 0 := ne_of_gt hB0
  have hinv0 : (0 : ℝ) ≤ B⁻¹ := by positivity
  have hinv1 : B⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    exact Or.inr hB
  have hterm : ∀ r : ℕ, (B ^ (r + 1))⁻¹ = B⁻¹ * (B⁻¹) ^ r := by
    intro r
    rw [pow_succ, mul_inv, ← inv_pow]
    ring
  rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_lt_one hinv0 hinv1]
  have hsub : (1 : ℝ) - B⁻¹ ≠ 0 := by
    have : (0 : ℝ) < 1 - B⁻¹ := by linarith
    exact ne_of_gt this
  have hBm : B - 1 ≠ 0 := by
    have : (0 : ℝ) < B - 1 := by linarith
    exact ne_of_gt this
  field_simp



                                                      

                                                                                           
                                                                                       
                                                                                       
                                                                                         







                                                     

                                                                                             
                                                                                           
                                                                                    
                                                                                           







                                         

                                                                                            
                                                                                              
                                                                                     
                                                        





                           

                                                                                 
                                                                                 
                                                                              



                                               

                                                                               
                                                                               
                                                                               
                                                                               
                                                 





end ErdosProblems.Erdos257.PaperCompleteR7

end


