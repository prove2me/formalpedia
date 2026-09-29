-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_integral_cubic_mod_five_density
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.integral_cubic_mod_five_density
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:58:49.985433+00:00
-- url     : https://prove2.me/theorems/2acc97ab-317c-4170-8ab2-1e61dcd0911b
-- title:
--   Lean source theorem: integral_cubic_mod_five_density
-- statement:
--   For integer numerator and denominator sequences obeying the recurrence from T, if m is nonzero modulo 5 and c≡m or −m modulo 5, disagreements with the profile m times the rising binomial coefficient plus c have lower density at least 1/5.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicModularDensity.lean#L76-L106
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
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

/-!
# Single-prime cubic obstructions without the window-length loss

A fixed prime p >= 3 supplies disjoint three-windows with
lower exceptional density 1/p, rather than 1/(3*p). A concrete modulo-five
corollary constructs the prime, root, and nonsquare witness. This corollary
is unconditional; it does not postulate a good-prime family.
-/

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.integral_cubic_mod_five_density
    (a u v : ℕ → ℤ) (m c : ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hm : (m : ZMod 5) ≠ 0)
    (hc : (c : ZMod 5) = (m : ZMod 5) ∨ (c : ZMod 5) = -(m : ZMod 5)) :
    LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / 5) := by sorry
