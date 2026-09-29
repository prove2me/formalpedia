-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_gcd_stabilises_of_not_quarter_density
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.cubic_gcd_stabilises_of_not_quarter_density
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:31:46.120139+00:00
-- url     : https://prove2.me/theorems/4c020cde-1c42-47a6-a976-0faa9599719e
-- title:
--   Lean source theorem: cubic_gcd_stabilises_of_not_quarter_density
-- statement:
--   Under the natural-coordinate recurrence, positive C, an integer-cleared rational cubic profile with A≠0, and disagreement density below the lower bound 1/4, the gcd of C(n) and D(n) becomes constant from some index onward.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicGcdFence.lean#L121-L137
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

theorem ErdosProblems.Erdos243.PaperCompleteR11.cubic_gcd_stabilises_of_not_quarter_density (a C D : ℕ → ℕ) (P : ℕ → ℚ)
    (q A B : ℤ) (hA : A ≠ 0) (hpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hclear : ∀ k : ℕ, (q : ℚ) * P k =
      (A : ℚ) * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + (B : ℚ))
    (hlow : ¬ LowerDensityAtLeast {n : ℕ | (C n : ℚ) ≠ P n} (1 / 4)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Nat.gcd (C n) (D n) = Nat.gcd (C N) (D N) := by sorry
