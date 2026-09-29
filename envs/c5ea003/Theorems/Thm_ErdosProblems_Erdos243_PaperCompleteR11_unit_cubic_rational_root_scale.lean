-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_unit_cubic_rational_root_scale
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.unit_cubic_rational_root_scale
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:07:22.787022+00:00
-- url     : https://prove2.me/theorems/740f9d85-63fa-41fc-8a65-4e738c41f569
-- title:
--   Lean source theorem: unit_cubic_rational_root_scale
-- statement:
--   For m>0, rational c=±1 and a rational root of m(r³−r)+6c=0, the scale m must be 1 or 16.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicRationalRoots.lean#L186-L200
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

theorem ErdosProblems.Erdos243.PaperCompleteR11.unit_cubic_rational_root_scale
    (m : ℕ) (c r : ℚ) (hm : 0 < m) (hc : c = 1 ∨ c = -1)
    (hroot : (m : ℚ) * (r ^ 3 - r) + 6 * c = 0) : m = 1 ∨ m = 16 := by sorry
