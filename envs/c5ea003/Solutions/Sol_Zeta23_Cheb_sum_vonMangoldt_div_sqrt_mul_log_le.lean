-- Prove2me | solution 1 for Zeta23.Cheb.sum_vonMangoldt_div_sqrt_mul_log_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:16:29.048437+00:00
-- url     : https://prove2.me/submissions/17d56f4f-6dfb-4ea0-809d-56b9a4d5d5af

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Theorems.Thm_Zeta23_Cheb_sum_one_div_sqrt_le
import Theorems.Thm_Zeta23_Cheb_sum_vonMangoldt_div_sqrt_le

-- from Zeta23.Chebyshev
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Chebyshev.lean — discharge of the Chebyshev-type hypothesis H-cheb.

Paper: "More than two thirds of the zeros of the Riemann zeta function lie on
the critical line", Lemma [lem:cheb], displays [eq:cheb1]–[eq:cheb2]:

  "For x ≥ 2,
     Σ_{n≤x} Λ(n) ≪ x,   Σ_{n≤x} Λ(n)/√n ≤ 3√x  (x ≥ x₀),
     Σ_{n≤x} Λ(n)/(√n log n) ≪ √x/log x,   Σ_{n≤x} Λ(n)² ≪ x log x,    [eq:cheb1]
     Σ_{n≤x} Λ(n)²/n = (log x)²/2 + O(log x),
     Σ_{n≤x} Λ(n)²/n (log x − log n) = (log x)³/6 + O((log x)²).       [eq:cheb2]"

H-cheb is classical [MV07 §2.2].  All sums here run over n ∈ Finset.Ioc 0 ⌊x⌋₊,
matching Mathlib's `Chebyshev.psi`.  The ≪-bounds are stated with explicit
existential constants; the paper's "≤ 3√x eventually" is provided in the robust
∃-constant form (the constant is not load-bearing downstream — [eq:Bdef] only
needs *some* B = l + C√X).

The two [eq:cheb2] asymptotics need Mertens' first theorem
Σ_{n≤x} Λ(n)/n = log x + O(1), which is not in Mathlib; it is supplied by
`mertensFirst` below, via Zeta23/FromPNTPlus/Mertens.lean.

Everything else comes from Mathlib (NumberTheory.Chebyshev ψ-bounds +
elementary induction/splitting arguments).
-/

namespace Zeta23
namespace Cheb

open Finset Real Chebyshev
open ArithmeticFunction hiding log
open scoped Nat.Prime

/-! ## [eq:cheb1], first bound: Σ_{n≤x} Λ(n) ≪ x -/


/-! ## [eq:cheb1], second bound: Σ_{n≤x} Λ(n)/√n ≪ √x -/


section Cheb1b

open MeasureTheory intervalIntegral





end Cheb1b





/-! ## [eq:cheb1], third bound: Σ_{n≤x} Λ(n)/(√n log n) ≪ √x/log x -/



/-! ## [eq:cheb1], fourth bound: Σ_{n≤x} Λ(n)² ≪ x log x -/



/-! ## [eq:cheb2]: the two Mertens-type asymptotics

Mertens' first theorem Σ_{n≤x} Λ(n)/n = log x + O(1) is supplied by
`Mertens.sum_mangoldt_div_eq_log` (see
Zeta23/FromPNTPlus/Mertens.lean), so both [eq:cheb2] bounds are unconditional. -/

section Cheb2

open MeasureTheory

















/-! ### The proper-prime-power defect

[lem:cheb] proof: "Σ_{n≤x} Λ(n)²/n = Σ_{n≤x} Λ(n) log n/n + O(1) (the two differ
only at proper prime powers)".  The defect Σ_{n≤x} Λ(n)(log n − Λ(n))/n is
supported on prime powers pᵏ with k ≥ 2, where its value is (k−1)log²p/pᵏ;
summing over all p, k bounds it by an absolute constant. -/















end Cheb2

end Cheb
end Zeta23
open Zeta23
open Cheb
open Finset Real Chebyshev
open ArithmeticFunction hiding log
open scoped Nat.Prime

theorem solution {x : ℝ} (hx : 2 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n) ≤
      (4 * Real.log 4 + 40) * Real.sqrt x / Real.log x := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hlx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  set R : ℕ := ⌊Real.sqrt x⌋₊ with hR
  have hsqx : Real.sqrt x ≤ x := (Real.sqrt_le_left hx0.le).mpr (by nlinarith)
  have hRle : R ≤ ⌊x⌋₊ := Nat.floor_le_floor hsqx
  have hsplit : (∑ n ∈ Ioc 0 R, Λ n / (Real.sqrt n * Real.log n))
      + ∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n) :=
    Finset.sum_Ioc_consecutive _ (Nat.zero_le R) hRle
  rw [← hsplit]
  -- part 1: n ≤ R = ⌊√x⌋
  have hpart1 : ∑ n ∈ Ioc 0 R, Λ n / (Real.sqrt n * Real.log n)
      ≤ 2 * Real.sqrt R := by
    refine le_trans (Finset.sum_le_sum fun n hn => ?_) (sum_one_div_sqrt_le R)
    obtain ⟨hn0, _⟩ := Finset.mem_Ioc.mp hn
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      simp [vonMangoldt_apply_one]
    · have hncast : (1 : ℝ) < (n : ℝ) := by exact_mod_cast h2.trans_lt' one_lt_two
      have hlogn : (0 : ℝ) < Real.log n := Real.log_pos hncast
      have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by positivity)
      calc Λ n / (Real.sqrt n * Real.log n)
          ≤ Real.log n / (Real.sqrt n * Real.log n) := by
            gcongr
            exact vonMangoldt_le_log
        _ = 1 / Real.sqrt n := by field_simp
  have hq : x ^ ((4 : ℝ)⁻¹) * x ^ ((4 : ℝ)⁻¹) = Real.sqrt x := by
    rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]; norm_num
  have h14nn : (0 : ℝ) ≤ x ^ ((4 : ℝ)⁻¹) := Real.rpow_nonneg hx0.le _
  have hsqR : Real.sqrt R ≤ x ^ ((4 : ℝ)⁻¹) := by
    have h1 : Real.sqrt (R : ℝ) ≤ Real.sqrt (Real.sqrt x) :=
      Real.sqrt_le_sqrt (Nat.floor_le (Real.sqrt_nonneg x))
    have h2 : Real.sqrt (Real.sqrt x) = x ^ ((4 : ℝ)⁻¹) := by
      rw [Real.sqrt_eq_rpow (Real.sqrt x), Real.sqrt_eq_rpow x, ← Real.rpow_mul hx0.le]
      norm_num
    rwa [h2] at h1
  have hlog : Real.log x ≤ 4 * x ^ ((4 : ℝ)⁻¹) := by
    have h4 := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 4⁻¹)
    rw [div_eq_mul_inv, inv_inv] at h4
    linarith
  -- part 2: √x < n ≤ x
  have hS := sum_vonMangoldt_div_sqrt_le hx1
  have hsub : ∑ n ∈ Ioc R ⌊x⌋₊, Λ n / Real.sqrt n
      ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => ?_
    · exact Finset.Ioc_subset_Ioc (Nat.zero_le R) le_rfl
    · exact div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hpart2 : ∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)
      ≤ 2 / Real.log x * ((2 * Real.log 4 + 16) * Real.sqrt x) := by
    have step : ∀ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)
        ≤ 2 / Real.log x * (Λ n / Real.sqrt n) := by
      intro n hn
      obtain ⟨hnR, _⟩ := Finset.mem_Ioc.mp hn
      have hsx : Real.sqrt x < (n : ℝ) := by
        have := Nat.lt_floor_add_one (Real.sqrt x)
        have hn1 : (R : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hnR
        rw [hR] at hn1
        linarith
      have hsx0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
      have hn0 : (0 : ℝ) < (n : ℝ) := lt_trans hsx0 hsx
      have hlogn : Real.log x / 2 ≤ Real.log n := by
        have := Real.log_le_log hsx0 hsx.le
        rwa [Real.log_sqrt hx0.le] at this
      have hlogn0 : (0 : ℝ) < Real.log n := lt_of_lt_of_le (by positivity) hlogn
      have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn0
      have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
      have ha : (0 : ℝ) ≤ Λ n / Real.sqrt n := div_nonneg hΛ hsn.le
      have hL2 : (0 : ℝ) < Real.log x / 2 := by positivity
      calc Λ n / (Real.sqrt n * Real.log n)
          = (Λ n / Real.sqrt n) / Real.log n := by rw [div_div]
        _ ≤ (Λ n / Real.sqrt n) / (Real.log x / 2) := by
            rw [div_le_div_iff₀ hlogn0 hL2]
            exact mul_le_mul_of_nonneg_left hlogn ha
        _ = 2 / Real.log x * (Λ n / Real.sqrt n) := by
            rw [div_div_eq_mul_div]
            ring
    calc ∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)
        ≤ ∑ n ∈ Ioc R ⌊x⌋₊, 2 / Real.log x * (Λ n / Real.sqrt n) :=
          Finset.sum_le_sum step
      _ = 2 / Real.log x * ∑ n ∈ Ioc R ⌊x⌋₊, Λ n / Real.sqrt n := by
          rw [Finset.mul_sum]
      _ ≤ 2 / Real.log x * ((2 * Real.log 4 + 16) * Real.sqrt x) := by
          have h2l : (0 : ℝ) ≤ 2 / Real.log x := by positivity
          exact mul_le_mul_of_nonneg_left (le_trans hsub hS) h2l
  -- assemble: multiply through by log x
  rw [le_div_iff₀ hlx]
  have e2 : 2 / Real.log x * ((2 * Real.log 4 + 16) * Real.sqrt x) * Real.log x
      = 2 * ((2 * Real.log 4 + 16) * Real.sqrt x) := by
    field_simp
  have hp1log : (∑ n ∈ Ioc 0 R, Λ n / (Real.sqrt n * Real.log n)) * Real.log x
      ≤ 8 * Real.sqrt x := by
    have step1 : (∑ n ∈ Ioc 0 R, Λ n / (Real.sqrt n * Real.log n)) * Real.log x
        ≤ (2 * Real.sqrt R) * Real.log x :=
      mul_le_mul_of_nonneg_right hpart1 hlx.le
    have step2 : (2 * Real.sqrt R) * Real.log x ≤ (2 * x ^ ((4 : ℝ)⁻¹)) * (4 * x ^ ((4 : ℝ)⁻¹)) := by
      have hsR0 : (0 : ℝ) ≤ Real.sqrt R := Real.sqrt_nonneg _
      nlinarith [hsqR, hlog, hlx, h14nn]
    have step3 : (2 * x ^ ((4 : ℝ)⁻¹)) * (4 * x ^ ((4 : ℝ)⁻¹)) = 8 * Real.sqrt x := by
      rw [← hq]; ring
    linarith
  have hp2log : (∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)) * Real.log x
      ≤ 2 * ((2 * Real.log 4 + 16) * Real.sqrt x) := by
    calc (∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)) * Real.log x
        ≤ 2 / Real.log x * ((2 * Real.log 4 + 16) * Real.sqrt x) * Real.log x :=
          mul_le_mul_of_nonneg_right hpart2 hlx.le
      _ = 2 * ((2 * Real.log 4 + 16) * Real.sqrt x) := e2
  have hfin : (∑ n ∈ Ioc 0 R, Λ n / (Real.sqrt n * Real.log n)
      + ∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)) * Real.log x
      = (∑ n ∈ Ioc 0 R, Λ n / (Real.sqrt n * Real.log n)) * Real.log x
        + (∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)) * Real.log x := by ring
  rw [hfin]
  nlinarith [hp1log, hp2log]
