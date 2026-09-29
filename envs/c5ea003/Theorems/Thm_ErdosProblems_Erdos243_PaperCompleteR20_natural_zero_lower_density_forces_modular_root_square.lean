-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_natural_zero_lower_density_forces_modular_root_square
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.natural_zero_lower_density_forces_modular_root_square
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:45:47.540792+00:00
-- url     : https://prove2.me/theorems/1ae9bbbc-ee68-4db0-ad66-dc4cd1b68f73
-- title:
--   Lean source theorem: natural_zero_lower_density_forces_modular_root_square
-- statement:
--   For the stated numerator-denominator recurrences from index T onward, if the indices where the numerator differs from m times the rising-binomial profile plus c have zero lower density, then at any modular root r of m(r³−r)+6c=0 with 3mr nonzero modulo a prime p≥3, r²−1 is a square modulo p.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicModularSquareSpecialisation.lean#L37-L58
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicZeroDensityShape
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

namespace ErdosProblems.Erdos243.PaperCompleteR20
end ErdosProblems.Erdos243.PaperCompleteR20

/-!
# Erdős 243: modular square data forced by zero exceptional density

This is the exact local input to the Chebotarev specialisation.  If the cubic
profile has zero lower density of exceptions, every good finite-field root of
the depressed cubic has square `r² - 1`; otherwise the already proved
single-prime obstruction gives positive lower density immediately.
-/


open ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems.Erdos243.PaperCompleteR20

theorem ErdosProblems.Erdos243.PaperCompleteR20.natural_zero_lower_density_forces_modular_root_square
    (a u v : ℕ → ℕ) (m : ℕ) (c : ℤ) (T p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hzero : ZeroLowerDensity
      {n : ℕ | (u n : ℤ) ≠ (m : ℤ) * risingBinomial n + c})
    (r : ZMod p)
    (hroot : (m : ZMod p) * (r ^ 3 - r) + ((6 * c : ℤ) : ZMod p) = 0)
    (hfactor : 3 * (m : ZMod p) * r ≠ 0) :
    IsSquare (r ^ 2 - 1) := by sorry
