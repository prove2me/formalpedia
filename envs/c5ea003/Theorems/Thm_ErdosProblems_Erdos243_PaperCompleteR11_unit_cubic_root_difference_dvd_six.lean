-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_unit_cubic_root_difference_dvd_six
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.unit_cubic_root_difference_dvd_six
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:09:47.582977+00:00
-- url     : https://prove2.me/theorems/9a2f9597-2efb-40b3-ad4d-8b6d0f945994
-- title:
--   Lean source theorem: unit_cubic_root_difference_dvd_six
-- statement:
--   For coprime natural s,t, if s<t and ms(t²−s²)=6t³, then s(t²−s²) divides 6; if t<s and ms(s²−t²)=6t³, then s(s²−t²) divides 6.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicRationalRoots.lean#L34-L63
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

theorem ErdosProblems.Erdos243.PaperCompleteR11.unit_cubic_root_difference_dvd_six
    (m s t : ℕ) (hcop : Nat.Coprime s t)
    (heq : (s < t ∧ m * s * (t ^ 2 - s ^ 2) = 6 * t ^ 3) ∨
      (t < s ∧ m * s * (s ^ 2 - t ^ 2) = 6 * t ^ 3)) :
    (s < t ∧ s * (t ^ 2 - s ^ 2) ∣ 6) ∨
      (t < s ∧ s * (s ^ 2 - t ^ 2) ∣ 6) := by sorry
