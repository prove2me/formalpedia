-- Prove2me | Definitions.Def_Sieve_Selberg_defs
-- name    : Sieve_Selberg_defs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-07-29T14:41:24.613854+00:00
-- url     : https://prove2.me/theorems/7a0ead70-0dfe-4486-844b-9562c6ad0305
-- title:
--   The Selberg sieve: bounding sum $S$, optimal weights $\gamma_d$, the $\mu^+ = \lambda^2(\gamma)$ majorant, and the Selberg upper-bound sieve
-- statement:
--   This bundle constructs the Selberg $\Lambda^2$ upper-bound sieve for a Selberg sieve structure $s$ with density $\nu$, sifting modulus $P$, Selberg terms $g$, and level $y$.
--
--   **Main definitions.**
--
--   - `selbergBoundingSum s` — the bounding sum $S = \sum_{l \mid P,\ l^2 \le y} g(l)$, where $g(l) = \nu(l)\prod_{p \mid l}(1-\nu(p))^{-1}$. The theorems `selbergBoundingSum_pos` and `selbergBoundingSum_ne_zero` record $S > 0$, so $S^{-1}$ is well-defined; $X/S$ is the main term of the Selberg bound.
--
--   - `selbergWeights s` — Selberg's optimal weights $\gamma_d = \nu(d)^{-1} g(d)\,\mu(d)\,S^{-1} \sum_{m \mid P,\ (dm)^2 \le y,\ (m,d)=1} g(m)$ for $d \mid P$ (and $0$ otherwise), where $\mu$ is the Möbius function. These are the minimizers of the quadratic form arising in the $\lambda^2$ method, normalized so that $\gamma_1 = 1$ (`weight_one_of_selberg`).
--
--   - `selbergMuPlus s` — the induced majorant $\mu^+ = \lambda^2(\gamma)$, i.e. $\mu^+(d) = \sum_{\mathrm{lcm}(d_1,d_2) = d} \gamma_{d_1}\gamma_{d_2}$.
--
--   - `selbergUbSieve s` — the resulting `UpperBoundSieve` structure: $\mu^+$ bundled with the proof (via `upperMoebius_of_lambda_sq` and $\gamma_1 = 1$) that $\sum_{d \mid n}\mu^+(d) \ge [n = 1]$.
--
--   **Downstream use.** Feeding `selbergUbSieve` into the fundamental sieve inequality yields Selberg's bound $\#\{\text{unsifted elements}\} \le X/S + \sum_{d} |\lambda\text{-supported remainders}|$ (`selberg_bound_simple`); combined with the lower bounds on $S$ and remainder estimates, this proves the Brun–Titchmarsh theorem used in the PNT+ project.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Selberg.lean (definitions vendored from this file)

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

/-!
# The Selberg Sieve

This file proves `selberg_bound_simple`, the main theorem of the Selberg.
-/

set_option lang.lemmaCmd true

noncomputable section

open scoped BigOperators Classical SelbergSieve ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat SelbergSieve.UpperBoundSieve ArithmeticFunction SelbergSieve BoundingSieve

namespace SelbergSieve
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

@[simp]
def selbergBoundingSum : ℝ :=
  ∑ l ∈ divisors P, if l ^ 2 ≤ y then g l else 0

set_option quotPrecheck false
local notation3 "S" => SelbergSieve.selbergBoundingSum s

theorem selbergBoundingSum_pos :
    0 < S := by
  dsimp only [selbergBoundingSum]
  rw [← sum_filter]
  apply sum_pos;
  · intro l hl
    rw [mem_filter, mem_divisors] at hl
    · apply selbergTerms_pos _ _ (hl.1.1)
  · simp_rw [Finset.Nonempty, mem_filter]; use 1
    constructor
    · apply one_mem_divisors.mpr prodPrimes_ne_zero
    rw [cast_one, one_pow]
    exact s.one_le_level

theorem selbergBoundingSum_ne_zero : S ≠ 0 := by
  apply _root_.ne_of_gt
  exact s.selbergBoundingSum_pos


def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ P then
    (ν d)⁻¹ * g d * μ d * S⁻¹ *
      ∑ m ∈ divisors P, if (d * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
  else 0

-- This notation traditionally uses λ, which is unavailable in lean
set_option quotPrecheck false
local notation3 "γ" => SelbergSieve.selbergWeights s


--Important facts about the selberg weights


def selbergMuPlus : ℕ → ℝ :=
  lambdaSquared γ

set_option quotPrecheck false
local notation3 "μ⁺" => SelbergSieve.selbergMuPlus s

theorem weight_one_of_selberg : γ 1 = 1 := by
  dsimp only [selbergWeights]
  rw [if_pos (one_dvd P), s.nu_mult.left, (selbergTerms_mult _).map_one]
  simp only [inv_one, mul_one, isUnit_one, IsUnit.squarefree, moebius_apply_of_squarefree,
    cardFactors_one, _root_.pow_zero, Int.cast_one, selbergBoundingSum, one_mul,
    coprime_one_right_eq_true, and_true, cast_one]
  rw [inv_mul_cancel₀]
  convert s.selbergBoundingSum_ne_zero


def selbergUbSieve : UpperBoundSieve :=
  ⟨μ⁺, upperMoebius_of_lambda_sq γ (s.weight_one_of_selberg)⟩

-- proved for general lambda squared sieves


end SelbergSieve


