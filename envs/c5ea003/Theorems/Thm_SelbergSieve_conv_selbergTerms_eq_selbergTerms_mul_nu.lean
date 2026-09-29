-- Prove2me | Theorems.Thm_SelbergSieve_conv_selbergTerms_eq_selbergTerms_mul_nu
-- name    : SelbergSieve.conv_selbergTerms_eq_selbergTerms_mul_nu
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:53:07.832932+00:00
-- url     : https://prove2.me/theorems/edcb83aa-5681-4977-a2e7-fccd227354b3
-- title:
--   Divisor-sum identity for Selberg terms: $\sum_{l\mid d} g(l) = g(d)/\nu(d)$
-- statement:
--   Work in the Selberg sieve formalism: a sieve problem carries a squarefree level $P$ (the product of the primes being sifted), a multiplicative density function $\nu$ with $0<\nu(p)<1$ on primes $p\mid P$, and the associated Selberg terms $g$, the multiplicative function defined on divisors of $P$ by $g(l)=\nu(l)\prod_{p\mid l}\bigl(1-\nu(p)\bigr)^{-1}$. Let $d$ be a divisor of $P$. Then
--
--   $$\sum_{\substack{l\,\mid\, P\\ l\,\mid\, d}} g(l) \;=\; \frac{g(d)}{\nu(d)},$$
--
--   where the sum ranges over the divisors $l$ of $P$ that also divide $d$ (equivalently, over all divisors of $d$, since $d\mid P$ and $P$ is squarefree).
--
--   This is the classical convolution identity for the Selberg terms: both sides are multiplicative in $d$, and on a prime $p\mid P$ it reduces to $1+\frac{\nu(p)}{1-\nu(p)}=\frac{1}{1-\nu(p)}=\frac{g(p)}{\nu(p)}$.
--
--   In the Selberg sieve it is the key arithmetic input for diagonalizing the main-term quadratic form $\sum_{d_1,d_2}\lambda_{d_1}\lambda_{d_2}\nu([d_1,d_2])$ into a sum of squares weighted by $1/g(l)$, which is then minimized to obtain the sieve upper bound (e.g. Brun–Titchmarsh-type estimates).
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Basic.lean#L129-L144

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module sieve
-/
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Definitions.Def_Sieve_AuxResults_defs
import Definitions.Def_Sieve_Basic_defs

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

open Finset Real Nat Aux BoundingSieve

open SelbergSieve

variable (s : BoundingSieve)
local notation3 "ν" => BoundingSieve.nu (self := s)
local notation3 "P" => BoundingSieve.prodPrimes (self := s)
local notation3 "a" => BoundingSieve.weights (self := s)
local notation3 "X" => BoundingSieve.totalMass (self := s)
local notation3 "A" => BoundingSieve.support (self := s)
local notation3 "𝒜" => BoundingSieve.multSum (s := s)
local notation3 "R" => BoundingSieve.rem (s := s)

-- S = ∑_{l|P, l≤√y} g(l)
-- Used in statement of the simple form of the selberg bound

local notation3 "g" => SelbergSieve.selbergTerms s

local notation "δ" => delta

theorem SelbergSieve.conv_selbergTerms_eq_selbergTerms_mul_nu {d : ℕ} (hd : d ∣ P) :
    (∑ l ∈ divisors P, if l ∣ d then g l else 0) = g d * (ν d)⁻¹ := by sorry
