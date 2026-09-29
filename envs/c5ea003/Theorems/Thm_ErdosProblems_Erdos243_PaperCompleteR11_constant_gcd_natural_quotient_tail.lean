-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_constant_gcd_natural_quotient_tail
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.constant_gcd_natural_quotient_tail
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T20:46:59.909993+00:00
-- url     : https://prove2.me/theorems/91e59fcb-458c-4d49-b5c0-cc4260567720
-- title:
--   Lean source theorem: constant_gcd_natural_quotient_tail
-- statement:
--   For positive natural-number sequences C and D satisfying C(n+1)+D(n)=a(n)C(n) and D(n+1)=a(n)D(n), if their gcd is a fixed positive g from index N onward, then on that tail g divides both coordinates, the quotients are positive and coprime, and the same two recurrence equations hold exactly for the quotients.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicPrimitiveNormalisation.lean#L20-L57
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

theorem ErdosProblems.Erdos243.PaperCompleteR11.constant_gcd_natural_quotient_tail
    (a C D : ℕ → ℕ) (N g : ℕ) (hg : 0 < g)
    (hCpos : ∀ n, 0 < C n) (hDpos : ∀ n, 0 < D n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hG : ∀ n, N ≤ n → Nat.gcd (C n) (D n) = g) :
    ∀ n, N ≤ n →
      g ∣ C n ∧ g ∣ D n ∧ 0 < C n / g ∧ 0 < D n / g ∧
      Nat.Coprime (C n / g) (D n / g) ∧
      C (n + 1) / g + D n / g = a n * (C n / g) ∧
      D (n + 1) / g = a n * (D n / g) := by sorry
