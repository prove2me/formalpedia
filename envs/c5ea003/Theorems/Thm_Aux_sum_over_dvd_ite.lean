-- Prove2me | Theorems.Thm_Aux_sum_over_dvd_ite
-- name    : Aux.sum_over_dvd_ite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:51:38.43488+00:00
-- url     : https://prove2.me/theorems/af1213ff-16c1-4b36-81b8-e35a87349e5c
-- title:
--   Extending a sum over divisors of $n$ to divisors of a multiple $P$ via an indicator
-- statement:
--   Let $\alpha$ be a ring, let $P \neq 0$ be a natural number, let $n \mid P$, and let $f : \mathbb{N} \to \alpha$ be any function. Then a sum over the divisors of $n$ can be rewritten as a sum over the divisors of the larger modulus $P$, restricted by the divisibility condition $d \mid n$:
--   $$\sum_{d \mid n} f(d) \;=\; \sum_{d \mid P} \big[ d \mid n \big]\, f(d),$$
--   where $[d \mid n]$ denotes the indicator (an if-then-else selecting $f(d)$ when $d \mid n$ and $0$ otherwise).
--
--   Since $n \mid P$ and $P \neq 0$, every divisor of $n$ is a divisor of $P$, so the right-hand side simply re-indexes the left-hand sum inside a fixed common index set.
--
--   This re-indexing lemma is a workhorse in sieve computations: it puts all divisor sums over a common range $\{d : d \mid P\}$, which is a prerequisite for exchanging orders of summation and for the quadratic-form manipulations in the Selberg sieve.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/AuxResults.lean#L33-L36

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

theorem Aux.sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d ∈ n.divisors, f d = ∑ d ∈ P.divisors, if d ∣ n then f d else 0 := by sorry
