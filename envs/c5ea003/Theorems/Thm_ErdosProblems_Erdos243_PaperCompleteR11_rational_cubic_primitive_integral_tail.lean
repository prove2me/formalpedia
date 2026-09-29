-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_rational_cubic_primitive_integral_tail
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.rational_cubic_primitive_integral_tail
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:26:21.707874+00:00
-- url     : https://prove2.me/theorems/d0daebda-a2c0-4ccc-b8c2-8d9eb8ee802f
-- title:
--   Lean source theorem: rational_cubic_primitive_integral_tail
-- statement:
--   For a positive rational cubic profile κn(n+1)(n+2)+η and positive natural recurrence coordinates, if the disagreement set has no lower-density bound of 1/4, there are a tail N, positive constant gcd g, positive integer m and integer c with mg=6κ and cg=η, and m,c have a Bézout identity. On that tail the divided coordinates are positive and coprime, satisfy the same exact recurrence, and agreement with the original rational profile is equivalent at each original index to agreement of C(n)/g with m times the rising binomial coefficient plus c.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicPrimitiveNormalisation.lean#L98-L187
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
# Constructed primitive cubic tails below quarter density

The stabilising divisor, the exact
natural quotient recurrence, the integral profile coefficients, and their
Bezout certificate are produced from the original orbit. The index is never
reset: division by a fixed gcd does not replace n by n-N in the polynomial.

This eliminates a normalisation supplier, but does NOT prove that the primitive
constant is a unit. Integral primitive profiles with other constants remain in
the universal-density problem.
-/

open ErdosProblems.Erdos243.PaperCompleteR11

theorem ErdosProblems.Erdos243.PaperCompleteR11.rational_cubic_primitive_integral_tail
    (a C D : ℕ → ℕ) (κ η : ℚ) (hκ : 0 < κ)
    (hCpos : ∀ n, 0 < C n) (hDpos : ∀ n, 0 < D n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hlow : ¬ LowerDensityAtLeast
      {n : ℕ | (C n : ℚ) ≠ κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η}
      (1 / 4)) :
    ∃ (N g : ℕ) (m c : ℤ), 0 < g ∧ 0 < m ∧
      (m : ℚ) * (g : ℚ) = 6 * κ ∧ (c : ℚ) * (g : ℚ) = η ∧
      (∃ x y : ℤ, m * x + c * y = 1) ∧
      ∀ n, N ≤ n →
        Nat.gcd (C n) (D n) = g ∧
        0 < C n / g ∧ 0 < D n / g ∧
        Nat.Coprime (C n / g) (D n / g) ∧
        C (n + 1) / g + D n / g = a n * (C n / g) ∧
        D (n + 1) / g = a n * (D n / g) ∧
        ((C n : ℚ) = κ * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + η ↔
          ((C n / g : ℕ) : ℤ) = m * risingBinomial n + c) := by sorry
