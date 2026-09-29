-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_primitive_pair_profile_hit
-- name    : ErdosProblems.Erdos243.PaperCompleteR11.primitive_pair_profile_hit
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:08:00.219072+00:00
-- url     : https://prove2.me/theorems/af0b4433-c4b7-49b7-a355-40dcfee3ac56
-- title:
--   Lean source theorem: primitive_pair_profile_hit
-- statement:
--   If d≥2 divides both values of an integer profile P at n and n+1, while u(n) and u(n+1) are coprime, at least one of these two natural values of u differs from P.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR11/CubicDivisorObstruction.lean#L60-L78
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

theorem ErdosProblems.Erdos243.PaperCompleteR11.primitive_pair_profile_hit (u : ℕ → ℕ) (P : ℕ → ℤ) (n d : ℕ)
    (hd : 2 ≤ d) (hcop : Nat.Coprime (u n) (u (n + 1)))
    (h0 : (d : ℤ) ∣ P n) (h1 : (d : ℤ) ∣ P (n + 1)) :
    ∃ i : ℕ, i < 2 ∧ (u (n + i) : ℤ) ≠ P (n + i) := by sorry
