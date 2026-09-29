-- Prove2me | Theorems.Thm_BrunTitchmarsh_primesBetween_le
-- name    : BrunTitchmarsh.primesBetween_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:56:20.846594+00:00
-- url     : https://prove2.me/theorems/5563cf43-d706-418a-a9c8-a15c27fbc07b
-- title:
--   Sieve upper bound for primes in an interval: $\pi(x+y)-\pi(x) \le 2y/\log z + O(z\log^3 z)$
-- statement:
--   Let $x, y$ be real numbers and let $z > 1$. Write $\pi(x, x+y]$-style prime counting as $\mathrm{primesBetween}(x, x+y)$, the number of primes in the interval $[x, x+y]$. Then
--   $$\#\{p \text{ prime} : x \le p \le x + y\} \;\le\; \frac{2y}{\log z} \;+\; 6\, z\,(1 + \log z)^3.$$
--
--   This is the raw output of the Selberg sieve applied to the interval $[x, x+y]$ with sifting level $z$: sifting by the primes below $z$ leaves at most $2y/\log z$ elements up to a remainder term, and the accumulated sieve remainders are bounded by $6 z (1+\log z)^3$ using divisor-sum estimates. Choosing $z$ appropriately (e.g. $z$ a small power of $y$) yields the Brun–Titchmarsh theorem $\pi(x+y) - \pi(x) \ll y/\log y$.
--
--   The result is the quantitative engine behind the Brun–Titchmarsh module of the PNT+ project: it gives an upper bound of the correct order of magnitude for primes in short intervals, uniform in the interval position $x$, which no zero-free-region argument provides.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/BrunTitchmarsh.lean#L248-L255

/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Primorial
import Batteries.Tactic.Lemma
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Topology.Order.Compact
import Definitions.Def_BrunTitchmarsh_defs
import Definitions.Def_Sieve_AuxResults_defs
import Definitions.Def_Sieve_Basic_defs
import Definitions.Def_Sieve_SelbergBounds_defs
import Definitions.Def_Sieve_Selberg_defs

open Sieve SelbergSieve BoundingSieve
open Filter Asymptotics
open scoped Nat ArithmeticFunction BigOperators ArithmeticFunction.zeta ArithmeticFunction.omega

open BrunTitchmarsh

variable (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 1 ≤ z)

include hx hy

theorem BrunTitchmarsh.primesBetween_le (hz : 1 < z) :
    primesBetween x (x+y) ≤ 2 * y / Real.log z + 6 * z * (1 + Real.log z) ^ 3 := by sorry
