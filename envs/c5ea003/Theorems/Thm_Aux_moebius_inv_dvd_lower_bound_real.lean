-- Prove2me | Theorems.Thm_Aux_moebius_inv_dvd_lower_bound_real
-- name    : Aux.moebius_inv_dvd_lower_bound_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:51:51.045388+00:00
-- url     : https://prove2.me/theorems/6b027eec-ddfd-4caa-b213-8ee0f70f14b1
-- title:
--   Möbius orthogonality over divisors of a squarefree modulus (real-valued form)
-- statement:
--   Let $P$ be a squarefree natural number, let $m \mid P$, and let $l$ be any natural number. Then the Möbius sum over divisors $d$ of $P$ that are sandwiched between $l$ and $m$ collapses to a delta function:
--   $$\sum_{\substack{d \mid P \\ l \mid d,\; d \mid m}} \mu(d) \;=\; \begin{cases} \mu(l) & \text{if } l = m, \\ 0 & \text{otherwise,} \end{cases}$$
--   where $\mu$ is the Möbius function and the identity is asserted in the real numbers (the summand is $\mu(d)$ cast to $\mathbb{R}$, with an if-then-else selecting the divisors $d$ satisfying $l \mid d$ and $d \mid m$).
--
--   This is a divisor-restricted form of the fundamental orthogonality relation $\sum_{d \mid n} \mu(d) = [n = 1]$: writing $d = l e$ with $e \mid m/l$ reduces the sum to $\mu(l) \sum_{e \mid m/l} \mu(e)$, which vanishes unless $m/l = 1$.
--
--   In the Selberg sieve this identity is the key step in inverting the change of variables that diagonalizes the sieve quadratic form, allowing the sieve weights to be solved for explicitly.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/AuxResults.lean#L90-L94

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

theorem Aux.moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by sorry
