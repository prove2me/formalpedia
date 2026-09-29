-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_integral_cubic_single_prime_density
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.integral_cubic_single_prime_density
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:51:40.097439+00:00
-- url     : https://prove2.me/theorems/f602e806-64b4-4a35-a59c-6b9c1c7ec58e
-- title:
--   Lean source theorem: integral_cubic_single_prime_density
-- statement:
--   For a prime p≥3 and integer sequences obeying the recurrence from T, a residue r satisfying m(r³−r)+6c=0, 3mr≠0 and nonsquare r²−1 modulo p forces disagreements with m times the rising binomial coefficient plus c to have lower density at least 1/p.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicModularDensity.lean#L24-L52
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

theorem ErdosProblems.Erdos243.PaperCompleteR11.integral_cubic_single_prime_density
    (a u v : ℕ → ℤ) (m c : ℤ) (T p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (r : ZMod p)
    (hroot : (m : ZMod p) * (r ^ 3 - r) + ((6 * c : ℤ) : ZMod p) = 0)
    (hfactor : 3 * (m : ZMod p) * r ≠ 0) (hns : ¬ IsSquare (r ^ 2 - 1)) :
    LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / (p : ℝ)) := by sorry
