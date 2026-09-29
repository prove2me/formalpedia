-- Prove2me | solution 1 for Aux.multiplicative_zero_of_zero_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T16:14:38.736201+00:00
-- url     : https://prove2.me/submissions/3f636890-104f-4b67-bfb1-5d0a4d7707ad

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

open Aux in
theorem solution (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    {m n : ℕ} (h_sq : Squarefree n) (hmn : m ∣ n) (h_zero : f m = 0) : f n = 0 := by
  rcases hmn with ⟨k, rfl⟩
  simp only [MulZeroClass.zero_mul,
    h_mult.map_mul_of_coprime (coprime_of_squarefree_mul h_sq), h_zero]

-- Lemma 3.1 in Heath-Brown's notes

