-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_unit_cubic_root_nat_classification
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.unit_cubic_root_nat_classification
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:07:27.852797+00:00
-- url     : https://prove2.me/theorems/3b056bfa-100d-4558-8c0c-6e3fb75fb9ea
-- title:
--   Lean source theorem: unit_cubic_root_nat_classification
-- statement:
--   For positive coprime natural s,t, if s<t and ms(t²−s²)=6t³, or t<s and ms(s²−t²)=6t³, then (s,t,m)=(1,2,16) or (2,1,1).
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicRationalRoots.lean#L65-L114
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

theorem ErdosProblems.Erdos243.PaperCompleteR11.unit_cubic_root_nat_classification
    (m s t : ℕ) (hs : 0 < s) (ht : 0 < t) (hcop : Nat.Coprime s t)
    (heq : (s < t ∧ m * s * (t ^ 2 - s ^ 2) = 6 * t ^ 3) ∨
      (t < s ∧ m * s * (s ^ 2 - t ^ 2) = 6 * t ^ 3)) :
    (s = 1 ∧ t = 2 ∧ m = 16) ∨ (s = 2 ∧ t = 1 ∧ m = 1) := by sorry
