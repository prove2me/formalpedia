-- Prove2me | Definitions.Def_Sieve_AuxResults_defs
-- name    : Sieve_AuxResults_defs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-07-29T03:49:47.069717+00:00
-- url     : https://prove2.me/theorems/bc0c55b6-df79-49be-88b4-3922ddcd09b4
-- title:
--   Auxiliary divisor-sum lemmas for the Selberg sieve: conditional-sum exchange and $\lambda^2$ lcm-sum reindexing
-- statement:
--   This bundle collects auxiliary combinatorial identities about divisor sums that support the Selberg sieve development (ported from the Lean 3 `aux_results` module). It contains no new structures; its content is a pair of reusable summation lemmas in the `Aux` namespace, plus scaffolding for multiplicative arithmetic functions.
--
--   **Main results stated.**
--
--   - `ite_sum_zero` — the exchange identity $\bigl(\text{if } p \text{ then } \sum_{x \in s} f(x) \text{ else } 0\bigr) = \sum_{x \in s} (\text{if } p \text{ then } f(x) \text{ else } 0)$, letting a global condition be pushed inside a finite sum.
--
--   - `conv_lambda_sq_larger_sum` — the reindexing identity $\sum_{d \mid n} \sum_{d_1 \mid d} \sum_{d_2 \mid d} [d = \mathrm{lcm}(d_1, d_2)]\, f(d_1, d_2, d) = \sum_{d \mid n} \sum_{d_1 \mid n} \sum_{d_2 \mid n} [d = \mathrm{lcm}(d_1, d_2)]\, f(d_1, d_2, d)$: since the condition $d = \mathrm{lcm}(d_1,d_2)$ forces $d_1, d_2 \mid d$, the inner sums may be enlarged from divisors of $d$ to divisors of $n$. This is the key bookkeeping step for expanding the square in $\lambda^2$-sieves.
--
--   **Downstream use.** These identities are used to expand $\bigl(\sum_{d \mid n} \lambda_d\bigr)^2$ as a double divisor sum over $\mathrm{lcm}$-pairs, the computation at the heart of the Selberg $\Lambda^2$ upper-bound sieve and hence of the Brun–Titchmarsh theorem in this project.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/AuxResults.lean (definitions vendored from this file)

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

noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.omega

open Nat ArithmeticFunction Finset


namespace ArithmeticFunction.IsMultiplicative

variable {R : Type*}


end ArithmeticFunction.IsMultiplicative

namespace Aux

theorem ite_sum_zero {p : Prop} [Decidable p] (s : Finset ℕ) (f : ℕ → ℝ) :
    (if p then (∑ x ∈ s, f x) else 0) = ∑ x ∈ s, if p then f x else 0 := by
  split_ifs <;> simp

theorem conv_lambda_sq_larger_sum (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ d ∈ n.divisors,
        ∑ d1 ∈ d.divisors,
          ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0) =
      ∑ d ∈ n.divisors,
        ∑ d1 ∈ n.divisors,
          ∑ d2 ∈ n.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0 := by
  apply sum_congr rfl; intro d hd
  rw [mem_divisors] at hd
  simp_rw [←Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, sum_filter, ←ite_and, ite_sum_zero,
    ←ite_and]
  congr with d1
  congr with d2
  congr
  rw [eq_iff_iff]
  refine ⟨fun ⟨_, _, h⟩ ↦ h, ?_⟩
  rintro rfl
  exact ⟨Nat.dvd_lcm_left d1 d2, Nat.dvd_lcm_right d1 d2, rfl⟩


-- Lemma 3.1 in Heath-Brown's notes


end Aux


