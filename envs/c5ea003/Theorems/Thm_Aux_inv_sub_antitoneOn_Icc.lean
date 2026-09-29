-- Prove2me | Theorems.Thm_Aux_inv_sub_antitoneOn_Icc
-- name    : Aux.inv_sub_antitoneOn_Icc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:51:13.88014+00:00
-- url     : https://prove2.me/theorems/f2c82dd5-4457-42a9-9d57-2deb5fe55bfb
-- title:
--   $x \mapsto (x-c)^{-1}$ is antitone on an interval $[a,b]$ to the right of $c$
-- statement:
--   Let $R$ be a linearly ordered field (formally: a field with a linear order making it a strict ordered ring), and let $a, b, c \in R$ with $c < a$. Then the function
--   $$x \longmapsto \frac{1}{x - c}$$
--   is antitone (order-reversing) on the closed interval $[a, b]$: for $x \le y$ in $[a,b]$ one has $(y-c)^{-1} \le (x-c)^{-1}$.
--
--   The hypothesis $c < a$ guarantees that $x - c > 0$ throughout the interval, so the reciprocal is well behaved and decreasing.
--
--   This small monotonicity fact is used in the sieve-theoretic auxiliary estimates of the PNT+ project, for instance when comparing sums of reciprocals against integrals; it is stated over a general ordered field for reusability.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/AuxResults.lean#L118-L124

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

theorem Aux.inv_sub_antitoneOn_Icc
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b c : R) (ha : c < a) :
    AntitoneOn (fun x ↦ (x-c)⁻¹) (Set.Icc a b) := by sorry
