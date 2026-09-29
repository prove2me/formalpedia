-- Prove2me | solution 1 for Zeta23.Cheb.sum_vonMangoldt_div_sqrt_le_three_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:19:23.444686+00:00
-- url     : https://prove2.me/submissions/43582743-9200-4e71-bae2-03b210f12964

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
import Theorems.Thm_Zeta23_Cheb_sum_vonMangoldt_div_sqrt_le_precise

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

theorem solution {x : ℝ}
    (hx : max 1 ((48 / (3 - 2 * Real.log 4)) ^ 4) ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n ≤ 3 * Real.sqrt x := by
  have hlog4lt : Real.log 4 < 3 / 2 := by
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [h2]; nlinarith [Real.log_two_lt_d9]
  set c : ℝ := 3 - 2 * Real.log 4 with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hx' : max 1 ((48 / c) ^ 4) ≤ x := by rw [hc]; exact hx

  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_left _ _) hx'
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have h := sum_vonMangoldt_div_sqrt_le_precise hx1
  have hlog8 : Real.log x ≤ 8 * x ^ ((8 : ℝ)⁻¹) := by
    have h8 := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 8⁻¹)
    rw [div_eq_mul_inv, inv_inv] at h8
    linarith
  have h18nn : (0 : ℝ) ≤ x ^ ((8 : ℝ)⁻¹) := Real.rpow_nonneg hx0.le _
  have h14nn : (0 : ℝ) ≤ x ^ ((4 : ℝ)⁻¹) := Real.rpow_nonneg hx0.le _
  have hq8 : x ^ ((8 : ℝ)⁻¹) * x ^ ((8 : ℝ)⁻¹) = x ^ ((4 : ℝ)⁻¹) := by
    rw [← Real.rpow_add hx0]; norm_num
  have hsq : Real.log x ^ 2 ≤ 64 * x ^ ((4 : ℝ)⁻¹) := by
    nlinarith [hlog8, Real.log_nonneg hx1, hq8, h18nn]
  have h84 : x ^ ((8 : ℝ)⁻¹) ≤ x ^ ((4 : ℝ)⁻¹) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hbound : 2 * Real.log x + Real.log x ^ 2 / 2 ≤ 48 * x ^ ((4 : ℝ)⁻¹) := by
    nlinarith [hlog8, hsq, h84]
  have hxc : (48 / c) ^ 4 ≤ x := le_trans (le_max_right _ _) hx'
  have h48nn : (0 : ℝ) ≤ 48 / c := by positivity
  have hx14 : 48 / c ≤ x ^ ((4 : ℝ)⁻¹) := by
    have hmono := Real.rpow_le_rpow (by positivity) hxc (by norm_num : (0 : ℝ) ≤ 4⁻¹)
    rwa [← Real.rpow_natCast (48 / c) 4, ← Real.rpow_mul h48nn,
      (by norm_num : ((4 : ℕ) : ℝ) * (4 : ℝ)⁻¹ = 1), Real.rpow_one] at hmono
  have hsqrt : Real.sqrt x = x ^ ((4 : ℝ)⁻¹) * x ^ ((4 : ℝ)⁻¹) := by
    rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]; norm_num
  have hkey : 48 * x ^ ((4 : ℝ)⁻¹) ≤ c * Real.sqrt x := by
    rw [hsqrt]
    have hc48 : c * (48 / c) = 48 := by field_simp
    have h1 : (48 : ℝ) ≤ c * x ^ ((4 : ℝ)⁻¹) := by
      have h2 := mul_le_mul_of_nonneg_left hx14 hcpos.le
      rwa [hc48] at h2
    calc 48 * x ^ ((4 : ℝ)⁻¹) ≤ (c * x ^ ((4 : ℝ)⁻¹)) * x ^ ((4 : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_right h1 h14nn
      _ = c * (x ^ ((4 : ℝ)⁻¹) * x ^ ((4 : ℝ)⁻¹)) := by ring
  nlinarith [h, hbound, hkey, hc]
