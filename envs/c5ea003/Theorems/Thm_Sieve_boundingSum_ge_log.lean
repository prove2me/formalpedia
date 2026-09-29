-- Prove2me | Theorems.Thm_Sieve_boundingSum_ge_log
-- name    : Sieve.boundingSum_ge_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:54:42.685754+00:00
-- url     : https://prove2.me/theorems/2fa87801-985a-4589-9edc-ef3e8e4ad647
-- title:
--   Lower bound $S \ge \tfrac{1}{2}\log y$ for the Selberg bounding sum with density $\nu(d) = 1/d$
-- statement:
--   Let $s$ be a Selberg sieve whose density function is $\nu(d) = 1/d$ (formally, the arithmetic function $\zeta$ divided pointwise by the identity), and suppose the sieving set is complete up to the level: every prime $p \le y$ divides the product of sieving primes $P$, where $y$ is the level of the sieve. Let $S = \sum_{l \mid P,\, l \le \sqrt{y}} g(l)$ denote the Selberg bounding sum attached to these data.
--
--   Then the bounding sum is at least half a logarithm of the level:
--
--   $$S \;\ge\; \frac{\log y}{2}.$$
--
--   Since the main term of the Selberg sieve is $X / S$, this lower bound converts the abstract sieve inequality into a concrete estimate of Chebyshev / Brun–Titchmarsh type: sifting the integers in an interval by all primes up to $\sqrt{y}$ leaves at most about $2X/\log y$ elements. It is the quantitative heart of the sieve-theoretic upper bound $\pi(x) \ll x / \log x$ used in the PNT+ project.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/SelbergBounds.lean#L496-L507

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Batteries.Tactic.Lemma
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.SelbergSieve
import Definitions.Def_Sieve_AuxResults_defs
import Definitions.Def_Sieve_Basic_defs
import Definitions.Def_Sieve_SelbergBounds_defs
import Definitions.Def_Sieve_Selberg_defs
/-!
# Bounds for the Selberg sieve
This file proves a number of results to help bound `Sieve.selbergSum`

## Main Results
* `selbergBoundingSum_ge_sum_div`: If `ν` is completely multiplicative then `S ≥ ∑_{n ≤ √y}, ν n`
* `boundingSum_ge_log`: If `ν n = 1 / n` then `S ≥ log y / 2`
* `rem_sum_le_of_const`: If `R_d ≤ C` then the error term is at most `C * y * (1 + log y)^3`
-/

set_option lang.lemmaCmd true

open scoped Nat ArithmeticFunction BigOperators Classical ArithmeticFunction.zeta
  ArithmeticFunction.omega
open BoundingSieve SelbergSieve

open Sieve

open CompletelyMultiplicative
open ArithmeticFunction

/-
Proposed generalisation :

theorem selbergBoundingSum_ge_sum_div (s : SelbergSieve)
    (hnu : CompletelyMultiplicative s.nuDivSelf) (hnu_nonneg : ∀ n, 0 ≤ s.nuDivSelf n)
    (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nuDivSelf p < 1):
    s.selbergBoundingSum ≥ ∑ m in
      (Finset.Icc 1 (Nat.floor <| Real.sqrt s.level)).filter (fun m => ∀ p, p.Prime → p ∣ m → p ∣ s.prodPrimes),
      s.nu m
-/

theorem Sieve.boundingSum_ge_log (s : SelbergSieve) (hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id)
  (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes)  :
    s.selbergBoundingSum ≥ Real.log (s.level) / 2 := by sorry
