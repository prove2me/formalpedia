-- Prove2me | Theorems.Thm_Aux_multiplicative_zero_of_zero_dvd
-- name    : Aux.multiplicative_zero_of_zero_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:52:04.274635+00:00
-- url     : https://prove2.me/theorems/5366ee15-f217-4d6c-a621-61aa4e4dfa70
-- title:
--   A multiplicative function vanishing at a divisor vanishes at a squarefree multiple
-- statement:
--   Let $f$ be a real-valued multiplicative arithmetic function ($f(1)=1$ and $f(ab) = f(a)f(b)$ for coprime $a, b$). Suppose $n$ is squarefree, $m \mid n$, and $f(m) = 0$. Then
--   $$f(n) = 0.$$
--
--   Because $n$ is squarefree, $m$ and $n/m$ are coprime, so $f(n) = f(m)\, f(n/m) = 0$. The squarefreeness hypothesis is essential: without it $m$ and $n/m$ need not be coprime and no such factorization is available.
--
--   This vanishing-propagation lemma is used in the sieve machinery to handle degenerate divisors uniformly, e.g. to show that support conditions on sieve density functions are inherited by multiples within the (squarefree) sifting range.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/AuxResults.lean#L96-L100

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

theorem Aux.multiplicative_zero_of_zero_dvd (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    {m n : ℕ} (h_sq : Squarefree n) (hmn : m ∣ n) (h_zero : f m = 0) : f n = 0 := by sorry
