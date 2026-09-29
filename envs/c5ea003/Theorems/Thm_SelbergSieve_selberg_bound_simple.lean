-- Prove2me | Theorems.Thm_SelbergSieve_selberg_bound_simple
-- name    : SelbergSieve.selberg_bound_simple
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:54:21.154254+00:00
-- url     : https://prove2.me/theorems/eafe2db7-b210-4b11-b11f-4cba698cbb14
-- title:
--   The fundamental theorem of the Selberg sieve: $S(A, P) \le X/S + \sum_{d \le y,\, d \mid P} 3^{\omega(d)} |R_d|$
-- statement:
--   Let $s$ be a Selberg sieve problem: a finite weighted set $A$ of total approximate mass $X$, a squarefree product $P$ of the primes being sieved, a multiplicative density function $\nu$, remainder terms $R_d$ measuring the error in the approximation $\sum_{d \mid n,\, n \in A} a_n \approx \nu(d) X$, and a sieve level $y \ge 1$. Write $S(A, P)$ for the *sifted sum*, the total weight of elements of $A$ coprime to $P$; write $S = \sum_{l \mid P,\, l \le \sqrt{y}} g(l)$ for the Selberg bounding sum built from the Selberg terms $g$; and write $\omega(d)$ for the number of distinct prime factors of $d$.
--
--   The Selberg upper bound sieve then gives:
--
--   $$S(A, P) \;\le\; \frac{X}{S} \;+\; \sum_{\substack{d \mid P \\ d \le y}} 3^{\omega(d)} \, |R_d|.$$
--
--   This is the fundamental theorem of the Selberg sieve in its classical textbook form: the optimized $\Lambda^2$ weights produce the main term $X/S$, while the accumulated remainders are controlled by the standard $3^{\omega(d)}$-weighted error sum over divisors of $P$ up to the level $y$. In the PNT+ project it is the engine behind Brun–Titchmarsh-type estimates such as the Chebyshev-type upper bound on primes in intervals, and it is reusable for any application fitting the axiomatic sieve framework.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Selberg.lean#L436-L447

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module selberg
-/
import Batteries.Tactic.Lemma
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.SelbergSieve
import Definitions.Def_Sieve_AuxResults_defs
import Definitions.Def_Sieve_Basic_defs
import Definitions.Def_Sieve_Selberg_defs

/-!
# The Selberg Sieve

This file proves `selberg_bound_simple`, the main theorem of the Selberg.
-/

set_option lang.lemmaCmd true

open scoped BigOperators Classical SelbergSieve ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat SelbergSieve.UpperBoundSieve ArithmeticFunction SelbergSieve BoundingSieve

open SelbergSieve
set_option quotPrecheck false

variable (s : SelbergSieve)
local notation3 "ν" => BoundingSieve.nu (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "P" => BoundingSieve.prodPrimes (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "a" => BoundingSieve.weights (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "X" => BoundingSieve.totalMass (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "A" => BoundingSieve.support (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "𝒜" => BoundingSieve.multSum (s := SelbergSieve.toBoundingSieve (self := s))
local notation3 "R" => BoundingSieve.rem (s := SelbergSieve.toBoundingSieve (self := s))
local notation3 "g" => SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))
local notation3 "y" => SelbergSieve.level (self := s)
local notation3 "hy" => SelbergSieve.one_le_level (self := s)

set_option quotPrecheck false
local notation3 "S" => SelbergSieve.selbergBoundingSum s

-- This notation traditionally uses λ, which is unavailable in lean
set_option quotPrecheck false
local notation3 "γ" => SelbergSieve.selbergWeights s

--Important facts about the selberg weights

set_option quotPrecheck false
local notation3 "μ⁺" => SelbergSieve.selbergMuPlus s

theorem SelbergSieve.selberg_bound_simple :
    siftedSum (s := s.toBoundingSieve) ≤
      X / S +
        ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by sorry
