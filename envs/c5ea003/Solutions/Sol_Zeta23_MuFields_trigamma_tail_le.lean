-- Prove2me | solution 1 for Zeta23.MuFields.trigamma_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:16:27.626871+00:00
-- url     : https://prove2.me/submissions/cbed7572-174c-424a-affe-b807b946ceda

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_GammaFacts_Series

-- from Zeta23.GammaFacts.Mu
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts/Mu.lean — the remaining H-Γ fields from the digamma series.  Canonical text: the paper [eq:mufacts]:
"μ is even, smooth, increasing in |τ|, μ ≥ μ(0) > −1, μ(τ) = (1/2π)log(|τ|/2π)
+ O(τ⁻²), μ′(τ) ≪ |τ|⁻¹ (|τ| ≥ 1)" plus the [eq:muints] integrals.
The ψ-toolkit is developed at a parametrized abscissa
a ∈ (0,1) (covers ζ's a = 1/4 and, composed with the recurrence, Theorem E's
a = 1/4 + κ/2).  Foundation: Zeta23.DigammaSeries.
-/

noncomputable section

namespace Zeta23
namespace MuFields

open Complex Filter Topology

variable {a : ℝ}






/-! ### Monotonicity on the vertical line, and the μ order facts -/






/-! ### The derivative bound μ′ ≪ 1/|τ|  (via the trigamma series) -/




end MuFields
end Zeta23
end
open Zeta23
open Complex Filter Topology
variable {a : ℝ}

theorem solution {t : ℝ} (ht : 1 / 2 ≤ |t|) :
    ∑' n : ℕ, (((1 / 4 : ℝ) + n) ^ 2 + t ^ 2)⁻¹ ≤ 12 / |t| := by
  have ht0 : (0 : ℝ) < |t| := by linarith
  have htsq : (0 : ℝ) < t ^ 2 := by
    have := sq_abs t
    nlinarith
  set N : ℕ := ⌈|t|⌉₊ + 2 with hN
  have hNt : |t| ≤ (N : ℝ) := by
    calc |t| ≤ (⌈|t|⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (N : ℝ) := by
          rw [hN]
          push_cast
          linarith
  have hNle : (N : ℝ) ≤ |t| + 3 := by
    rw [hN]
    push_cast
    have := Nat.ceil_lt_add_one (abs_nonneg t)
    linarith
  have hsummable : Summable (fun n : ℕ => (((1 / 4 : ℝ) + n) ^ 2 + t ^ 2)⁻¹) := by
    refine Summable.of_norm_bounded_eventually
      (g := fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) ?_ ?_
    · have h3 := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
      have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
        funext n
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rwa [heq] at h3
    · rw [Nat.cofinite_eq_atTop]
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr
      nlinarith
  rw [← hsummable.sum_add_tsum_nat_add N]
  have hhead : ∑ i ∈ Finset.range N, (((1 / 4 : ℝ) + i) ^ 2 + t ^ 2)⁻¹
      ≤ (N : ℝ) * (t ^ 2)⁻¹ := by
    have h1 : ∀ i ∈ Finset.range N, (((1 / 4 : ℝ) + i) ^ 2 + t ^ 2)⁻¹ ≤ (t ^ 2)⁻¹ := by
      intro i _
      gcongr
      nlinarith [sq_nonneg ((1 / 4 : ℝ) + i)]
    calc ∑ i ∈ Finset.range N, (((1 / 4 : ℝ) + i) ^ 2 + t ^ 2)⁻¹
        ≤ ∑ _i ∈ Finset.range N, (t ^ 2)⁻¹ := Finset.sum_le_sum h1
      _ = (N : ℝ) * (t ^ 2)⁻¹ := by
          rw [Finset.sum_const, Finset.card_range]
          simp [nsmul_eq_mul]
  have htail : ∑' i : ℕ, (((1 / 4 : ℝ) + ((i + N : ℕ) : ℝ)) ^ 2 + t ^ 2)⁻¹
      ≤ ((N : ℝ) - 1)⁻¹ := by
    have hN2 : (2 : ℕ) ≤ N := by
      rw [hN]
      omega
    push_cast
    refine Real.tsum_le_of_sum_range_le (fun n => by positivity) fun K => ?_
    have hterm : ∀ i : ℕ, (((1 / 4 : ℝ) + (i + N)) ^ 2 + t ^ 2)⁻¹
        ≤ ((i : ℝ) + N - 1)⁻¹ - ((i : ℝ) + N)⁻¹ := by
      intro i
      have hiN1 : (1 : ℝ) ≤ (i : ℝ) + N - 1 := by
        have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
        have := Nat.cast_nonneg (α := ℝ) i
        linarith
      have hpos1 : (0 : ℝ) < (i : ℝ) + N - 1 := by linarith
      have hpos2 : (0 : ℝ) < (i : ℝ) + N := by linarith
      have hsub : ((i : ℝ) + N - 1)⁻¹ - ((i : ℝ) + N)⁻¹
          = (((i : ℝ) + N - 1) * ((i : ℝ) + N))⁻¹ := by
        rw [inv_sub_inv hpos1.ne' hpos2.ne']
        ring_nf
      rw [hsub]
      have hd1 : (0 : ℝ) < ((i : ℝ) + N - 1) * ((i : ℝ) + N) := mul_pos hpos1 hpos2
      have hd2 : ((i : ℝ) + N - 1) * ((i : ℝ) + N)
          ≤ ((1 / 4 : ℝ) + ((i : ℝ) + (N : ℝ))) ^ 2 + t ^ 2 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) i, sq_nonneg t]
      have h3 := one_div_le_one_div_of_le hd1 hd2
      simpa [one_div] using h3
    calc ∑ i ∈ Finset.range K, (((1 / 4 : ℝ) + (i + N)) ^ 2 + t ^ 2)⁻¹
        ≤ ∑ i ∈ Finset.range K, (((i : ℝ) + N - 1)⁻¹ - ((i : ℝ) + N)⁻¹) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = ((N : ℝ) - 1)⁻¹ - ((K : ℝ) + N - 1)⁻¹ := by
          have htel := Finset.sum_range_sub' (f := fun i : ℕ => ((i : ℝ) + N - 1)⁻¹) K
          simp only [Nat.cast_zero, zero_add] at htel
          rw [← htel]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hx : (((i + 1 : ℕ) : ℝ) + N - 1)⁻¹ = ((i : ℝ) + N)⁻¹ := by
            push_cast
            ring_nf
          rw [hx]
      _ ≤ ((N : ℝ) - 1)⁻¹ := by
          have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
          have : (0 : ℝ) < (K : ℝ) + N - 1 := by
            have := Nat.cast_nonneg (α := ℝ) K
            linarith
          have : (0 : ℝ) ≤ ((K : ℝ) + N - 1)⁻¹ := by positivity
          linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have h2 : (2 : ℕ) ≤ N := by
      rw [hN]
      omega
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
    linarith
  have hNm1 : |t| ≤ (N : ℝ) - 1 := by
    rw [hN]
    push_cast
    have := Nat.le_ceil |t|
    linarith
  have htail2 : ((N : ℝ) - 1)⁻¹ ≤ |t|⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le ht0 hNm1
  have hhead2 : (N : ℝ) * (t ^ 2)⁻¹ ≤ 10 / |t| := by
    have hts : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    rw [hts]
    rw [div_eq_mul_inv]
    have h1 : (N : ℝ) ≤ 7 * |t| := by linarith
    calc (N : ℝ) * ((|t| ^ 2)⁻¹) ≤ 7 * |t| * ((|t| ^ 2)⁻¹) := by
          gcongr
      _ = 7 * |t|⁻¹ := by
          field_simp
      _ ≤ 10 * |t|⁻¹ := by
          have : (0 : ℝ) ≤ |t|⁻¹ := by positivity
          linarith
  calc (∑ i ∈ Finset.range N, (((1 / 4 : ℝ) + i) ^ 2 + t ^ 2)⁻¹)
        + ∑' i : ℕ, (((1 / 4 : ℝ) + ((i + N : ℕ) : ℝ)) ^ 2 + t ^ 2)⁻¹
      ≤ (N : ℝ) * (t ^ 2)⁻¹ + ((N : ℝ) - 1)⁻¹ := add_le_add hhead htail
    _ ≤ 10 / |t| + |t|⁻¹ := add_le_add hhead2 htail2
    _ ≤ 12 / |t| := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have : (0 : ℝ) ≤ |t|⁻¹ := by positivity
        linarith
