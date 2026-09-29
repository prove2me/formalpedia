-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.integral_cubic_quartic_prime_density
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:03:17.589261+00:00
-- url     : https://prove2.me/submissions/f6233b18-aa95-4ccd-9648-c425007746ca

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicQuarticWindows
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_disjoint_periodic_lowerDensity
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_integral_cubic_quartic_window_hit
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

   
                                                 

                                                                              
                                                    
                         
                                                                            
                                                                            
  

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (a u v : ℕ → ℤ) (m c : ℤ) (T p : ℕ) [Fact p.Prime] (hp : 4 ≤ p)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (r : ZMod p) (hm : (m : ZMod p) ≠ 0)
    (hroot : (m : ZMod p) * (r ^ 3 - r) + ((6 * c : ℤ) : ZMod p) = 0)
    (hcert : CubicQuarticNonresidue r) :
    LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / (p : ℝ)) := by
  letI : NeZero p := ⟨by omega⟩
  let start := (r - 3).val + p * T
  apply disjoint_periodic_lowerDensity _ start p 4 (by omega) hp
  intro k
  have hT : T ≤ start + p * k := by
    have hmul := Nat.mul_le_mul_right T (show 1 ≤ p by omega)
    dsimp [start]
    omega
  have hphase : ((start + p * k : ℕ) : ZMod p) = r - 3 := by
    simp [start, ZMod.natCast_zmod_val]
  exact integral_cubic_quartic_window_hit a u v m c T (start + p * k) p
    hT hnum hden r hm hroot hcert hphase
