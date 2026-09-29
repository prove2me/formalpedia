-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_integral_cubic_quartic_ratio_density
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.integral_cubic_quartic_ratio_density
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:02:01.520375+00:00
-- url     : https://prove2.me/theorems/f3026482-e79d-4a68-8a37-9d69ca43bb3d
-- title:
--   Lean source theorem: integral_cubic_quartic_ratio_density
-- statement:
--   For a prime p≥4 and integer sequences obeying the recurrence from T, if m is nonzero modulo p and the residue c/m has a cubic quartic witness, disagreements with m times the rising binomial coefficient plus c have lower density at least 1/p.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicQuarticWindows.lean#L174-L186
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicQuarticWindows
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring

   
                                                 

                                                                              
                                                    
                         
                                                                            
                                                                            
  

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.integral_cubic_quartic_ratio_density
    (a u v : ℕ → ℤ) (m c : ℤ) (T p : ℕ) [Fact p.Prime] (hp : 4 ≤ p)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hm : (m : ZMod p) ≠ 0)
    (hw : CubicQuarticWitness p ((c : ZMod p) / (m : ZMod p))) :
    LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / (p : ℝ)) := by sorry
