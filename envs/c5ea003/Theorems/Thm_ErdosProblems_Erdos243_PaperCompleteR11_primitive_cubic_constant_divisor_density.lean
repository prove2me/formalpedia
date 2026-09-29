-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_primitive_cubic_constant_divisor_density
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.primitive_cubic_constant_divisor_density
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:18:15.801019+00:00
-- url     : https://prove2.me/theorems/ab7aed68-ccf7-44f4-ad27-459277c04b3e
-- title:
--   Lean source theorem: primitive_cubic_constant_divisor_density
-- statement:
--   If a natural sequence has coprime adjacent terms from T onward, d≥2 divides the integer constant c, and the comparison profile is m times the rising binomial coefficient plus c, then its disagreement set has lower density at least 1/(6d).
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicDivisorObstruction.lean#L103-L114
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
# Nonunit constants: explicit primitive divisor obstructions

The old 1/(12*d) loss is unnecessary for a single
periodic family of disjoint two-windows. We obtain 1/(6*d) for every d >= 2,
and 1/d when d is coprime to 6. In particular divisors 2, 3, and any divisor
between 2 and 28 coprime to 6 give the universal 1/28 bound in this branch.
This does not discard constants whose prime factors are all >= 29.
-/

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.primitive_cubic_constant_divisor_density (u : ℕ → ℕ) (m c : ℤ)
    (T d : ℕ) (hd : 2 ≤ d) (hdc : (d : ℤ) ∣ c)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (u (n + 1))) :
    LowerDensityAtLeast {n : ℕ | (u n : ℤ) ≠ m * risingBinomial n + c}
      (1 / ((6 * d : ℕ) : ℝ)) := by sorry
