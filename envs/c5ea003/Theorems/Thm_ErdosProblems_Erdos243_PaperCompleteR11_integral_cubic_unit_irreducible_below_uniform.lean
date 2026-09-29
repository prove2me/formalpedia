-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_integral_cubic_unit_irreducible_below_uniform
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.integral_cubic_unit_irreducible_below_uniform
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:14:52.550614+00:00
-- url     : https://prove2.me/theorems/3e7743d2-80c4-43b4-90b7-f77768b28af2
-- title:
--   Lean source theorem: integral_cubic_unit_irreducible_below_uniform
-- statement:
--   For a positive natural scale m and unit constant c=±1, if integer sequences obey the recurrence from T and disagreements with m times the rising binomial coefficient plus c have no lower-density bound of 1/28, then X³−X+6c/m is irreducible over ℚ.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicRationalRoots.lean#L249-L268
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Polynomial.SpecificDegree
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
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic
import Mathlib.Tactic.Ring

   
                                                                        

                                                                           
                                                                           
                                                                         
                                                                           
                                                                               
  

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.integral_cubic_unit_irreducible_below_uniform
    (a u v : ℕ → ℤ) (m : ℕ) (c : ℤ) (T : ℕ) (hm : 0 < m)
    (hc : c = 1 ∨ c = -1)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hlow : ¬ LowerDensityAtLeast {n : ℕ | u n ≠ (m : ℤ) * risingBinomial n + c}
      (1 / 28)) :
    Irreducible (cubicScalePolynomial (6 * (c : ℚ) / (m : ℚ))) := by sorry
