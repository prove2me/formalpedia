-- Prove2me | Theorems.Thm_Aux_div_mult_of_dvd_squarefree
-- name    : Aux.div_mult_of_dvd_squarefree
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:50:48.453315+00:00
-- url     : https://prove2.me/theorems/d58c99f7-330d-4336-a553-660e7dd2265c
-- title:
--   Quotient rule for multiplicative functions on divisors of a squarefree number
-- statement:
--   Let $f$ be a real-valued arithmetic function that is multiplicative, i.e. $f(1) = 1$ and $f(mn) = f(m)f(n)$ whenever $\gcd(m,n) = 1$. Let $l$ be a squarefree natural number, let $d \mid l$, and suppose $f(d) \neq 0$. Then division by $f(d)$ recovers the value of $f$ at the complementary divisor:
--   $$\frac{f(l)}{f(d)} = f\!\left(\frac{l}{d}\right).$$
--
--   Since $l$ is squarefree, the divisor $d$ and the cofactor $l/d$ are automatically coprime, so multiplicativity gives $f(l) = f(d)\,f(l/d)$, and the hypothesis $f(d) \neq 0$ lets one divide.
--
--   This is a basic manipulation lemma used throughout the Selberg sieve development: it allows sums over divisors of a squarefree sifting range to be re-parametrized by complementary divisors, a step that appears repeatedly when diagonalizing the sieve quadratic form.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/AuxResults.lean#L102-L108

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module aux_results
-/
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Definitions.Def_Sieve_AuxResults_defs

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.omega

open Nat ArithmeticFunction Finset

open ArithmeticFunction.IsMultiplicative

variable {R : Type*}

open Aux

theorem Aux.div_mult_of_dvd_squarefree (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    (l d : ℕ) (hdl : d ∣ l) (hl : Squarefree l) (hd : f d ≠ 0) : f l / f d = f (l / d) := by sorry
