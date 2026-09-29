-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_integral_cubic_quartic_window_hit
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.integral_cubic_quartic_window_hit
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:58:57.870151+00:00
-- url     : https://prove2.me/theorems/4f5bebf7-fa2f-4da1-9984-540ec9496531
-- title:
--   Lean source theorem: integral_cubic_quartic_window_hit
-- statement:
--   For integer sequences obeying the recurrence from T, if m is nonzero modulo prime p, r solves m(r³−r)+6c=0 modulo p and has a cubic quartic nonresidue certificate, then every four-index window starting at n≥T with n≡r−3 mod p contains a disagreement with m times the rising binomial coefficient plus c.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicQuarticWindows.lean#L69-L149
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

theorem ErdosProblems.Erdos243.PaperCompleteR11.integral_cubic_quartic_window_hit
    (a u v : ℕ → ℤ) (m c : ℤ) (T n p : ℕ) [Fact p.Prime]
    (hn : T ≤ n)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (r : ZMod p) (hm : (m : ZMod p) ≠ 0)
    (hroot : (m : ZMod p) * (r ^ 3 - r) + ((6 * c : ℤ) : ZMod p) = 0)
    (hcert : CubicQuarticNonresidue r) (hphase : (n : ZMod p) = r - 3) :
    ∃ j : ℕ, j < 4 ∧ u (n + j) ≠ m * risingBinomial (n + j) + c := by sorry
