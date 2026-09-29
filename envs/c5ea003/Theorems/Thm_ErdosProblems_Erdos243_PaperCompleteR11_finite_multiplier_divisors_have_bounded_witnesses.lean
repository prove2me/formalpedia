-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_finite_multiplier_divisors_have_bounded_witnesses
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.finite_multiplier_divisors_have_bounded_witnesses
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:48:06.490237+00:00
-- url     : https://prove2.me/theorems/9ee550e3-cd54-4b21-8342-4d479ce48beb
-- title:
--   Lean source theorem: finite_multiplier_divisors_have_bounded_witnesses
-- statement:
--   Given a sequence a, a starting index T and a divisor bound B, there is one finite index N such that every p≤B dividing some a(i) at i≥T already divides one with T≤i≤N.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/PrimitiveMultiplierSupply.lean#L136-L175
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicZeroDensityShape
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

theorem ErdosProblems.Erdos243.PaperCompleteR11.finite_multiplier_divisors_have_bounded_witnesses
    (a : ℕ → ℕ) (T B : ℕ) :
    ∃ N : ℕ, ∀ p : ℕ, p ≤ B → (∃ i, T ≤ i ∧ p ∣ a i) →
      ∃ i, T ≤ i ∧ i ≤ N ∧ p ∣ a i := by sorry
