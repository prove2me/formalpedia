-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_common_divisor_dvd_cubic_third_difference
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.common_divisor_dvd_cubic_third_difference
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T20:46:50.013682+00:00
-- url     : https://prove2.me/theorems/6508e427-7fd9-4994-9866-12a55c2e1d91
-- title:
--   A common divisor divides the cubic third difference
-- statement:
--   Under the displayed integer clearing of a rational cubic P, if C matches P at four consecutive indices and d divides those four values of C, then d divides 6A.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicGcdFence.lean#L38-L59
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring

/-!
# A uniform four-window gcd reduction for cubic profiles

The reduction works below density `1/4`, not only
under density zero. Four agreeing values give the exact third difference;
every earlier common divisor divides that difference. No upper growth estimate,
record restart, denominator reduction, or prime-existence hypothesis is needed.
-/

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.common_divisor_dvd_cubic_third_difference (C : ℕ → ℕ) (P : ℕ → ℚ)
    (q A B : ℤ) (n d : ℕ)
    (hclear : ∀ k : ℕ, (q : ℚ) * P k =
      (A : ℚ) * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + (B : ℚ))
    (hagree : ∀ j : ℕ, j < 4 → (C (n + j) : ℚ) = P (n + j))
    (hdiv : ∀ j : ℕ, j < 4 → d ∣ C (n + j)) :
    (d : ℤ) ∣ 6 * A := by sorry
