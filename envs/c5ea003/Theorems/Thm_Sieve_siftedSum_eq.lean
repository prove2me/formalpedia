-- Prove2me | Theorems.Thm_Sieve_siftedSum_eq
-- name    : Sieve.siftedSum_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:55:50.309029+00:00
-- url     : https://prove2.me/theorems/c1a55ea2-1ae5-45d8-973b-dffaea476df6
-- title:
--   The sifted sum with primorial modulus counts $z$-rough numbers in the support
-- statement:
--   Let $s$ be a Selberg sieve whose weights are identically $1$ on its finite support $A$, and let $z \ge 1$ be a real number such that the sieving modulus is the primorial $P = \lfloor z \rfloor\# = \prod_{p \le \lfloor z \rfloor} p$.
--
--   Then the sifted sum — the total weight of the elements of $A$ coprime to $P$ — is exactly the number of *$z$-rough* elements of the support:
--
--   $$S(A, P) \;=\; \#\{\, d \in A : p \nmid d \text{ for every prime } p \le z \,\}.$$
--
--   This identity grounds the abstract sieve machinery in its intended combinatorial meaning: with unit weights and a primorial modulus, sifting is literally counting the members of $A$ with no small prime factors. Combined with the fundamental Selberg bound and the lower bound on the bounding sum, it yields concrete upper bounds for counts of primes (every prime in $(z, x]$ is $z$-rough), i.e. Chebyshev–Brun–Titchmarsh estimates.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/SelbergBounds.lean#L79-L113

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

theorem Sieve.siftedSum_eq (s : SelbergSieve) (hw : ∀ i ∈ s.support, s.weights i = 1) (z : ℝ)
    (hz : 1 ≤ z) (hP : s.prodPrimes = primorial (Nat.floor z)) :
    siftedSum (s := s.toBoundingSieve) =
    (s.support.filter (fun d => ∀ p:ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card := by sorry
