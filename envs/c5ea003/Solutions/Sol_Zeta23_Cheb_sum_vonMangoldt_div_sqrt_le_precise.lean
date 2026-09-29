-- Prove2me | solution 1 for Zeta23.Cheb.sum_vonMangoldt_div_sqrt_le_precise
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:20:28.846574+00:00
-- url     : https://prove2.me/submissions/35e39dd3-1c11-4f80-b30d-79ac25a72e6f

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

lemma sum_Icc_eq_sum_Ioc {c : ℕ → ℝ} (hc : c 0 = 0) (n : ℕ) :
    ∑ k ∈ Icc 0 n, c k = ∑ k ∈ Ioc 0 n, c k := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, hc, zero_add]

lemma psi_eq_sum_Icc' (t : ℝ) :
    ∑ k ∈ Icc 0 ⌊t⌋₊, Λ k = Chebyshev.psi t := by
  rw [sum_Icc_eq_sum_Ioc (by simp) ⌊t⌋₊]; rfl

/-- Abel summation specialised to Σ_{n≤x} Λ(n)/√n, in terms of ψ. -/
lemma abel_sqrt {x : ℝ} (_hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n
      = x ^ (-(2⁻¹ : ℝ)) * Chebyshev.psi x
        + 2⁻¹ * ∫ t in Set.Ioc 1 x, t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t := by
  have hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) x,
      DifferentiableAt ℝ (fun t : ℝ => t ^ (-(2⁻¹ : ℝ))) t := fun t ht =>
    Real.differentiableAt_rpow_const_of_ne _ (by nlinarith [ht.1] : t ≠ 0)
  have hderiv : deriv (fun t : ℝ => t ^ (-(2⁻¹ : ℝ)))
      = fun t : ℝ => -(2⁻¹ : ℝ) * t ^ (-(2⁻¹ : ℝ) - 1) := Real.deriv_rpow_const' _
  have hf_int : IntegrableOn (deriv fun t : ℝ => t ^ (-(2⁻¹ : ℝ))) (Set.Icc 1 x) := by
    rw [hderiv]
    refine (ContinuousOn.mul continuousOn_const ?_).integrableOn_Icc
    intro t ht
    exact (Real.continuousAt_rpow_const t _
      (Or.inl (by nlinarith [ht.1] : t ≠ 0))).continuousWithinAt
  have habel := sum_mul_eq_sub_integral_mul₀ (fun n => Λ n) (by simp) x hf_diff hf_int
  have hL : ∑ k ∈ Icc 0 ⌊x⌋₊, (k : ℝ) ^ (-(2⁻¹ : ℝ)) * Λ k
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n := by
    rw [sum_Icc_eq_sum_Ioc (by simp) ⌊x⌋₊]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hrw : (k : ℝ) ^ (-(2⁻¹ : ℝ)) = (Real.sqrt k)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg k)]
      norm_num
    rw [hrw, div_eq_mul_inv, mul_comm]
  rw [hL, psi_eq_sum_Icc'] at habel
  have hI : (∫ t in Set.Ioc 1 x, deriv (fun t : ℝ => t ^ (-(2⁻¹ : ℝ))) t
        * ∑ k ∈ Icc 0 ⌊t⌋₊, (fun n => Λ n) k)
      = -(2⁻¹ : ℝ) * ∫ t in Set.Ioc 1 x, t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    simp only [hderiv]
    rw [← psi_eq_sum_Icc' t]
    ring
  rw [habel, hI]
  ring

/-- The tail integral bound: ∫₁ˣ t^{-3/2} ψ(t) dt ≤ log 4·(2√x − 2) + (log x)². -/
lemma integral_tail_bound {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioc 1 x, t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t
      ≤ Real.log 4 * (2 * Real.sqrt x - 2) + Real.log x ^ 2 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  -- the explicit dominating integrand
  set g : ℝ → ℝ := fun t => Real.log 4 * t ^ (-(2⁻¹ : ℝ)) + 2 * (Real.log t * t⁻¹) with hg
  have hcont_g : ContinuousOn g (Set.Icc 1 x) := by
    apply ContinuousOn.add
    · exact continuousOn_const.mul fun t ht =>
        (Real.continuousAt_rpow_const t _
          (Or.inl (by nlinarith [ht.1] : t ≠ 0))).continuousWithinAt
    · refine continuousOn_const.mul (ContinuousOn.mul ?_ ?_)
      · exact fun t ht => (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
      · exact continuousOn_inv₀.mono fun t ht => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          nlinarith [ht.1]
  -- step 1: pointwise comparison with g on Ioc 1 x
  have hpoint : ∀ t ∈ Set.Ioc (1 : ℝ) x,
      t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t ≤ g t := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := ht.1.le
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
    have hψ : Chebyshev.psi t ≤ Real.log 4 * t + 2 * Real.sqrt t * Real.log t :=
      Chebyshev.psi_le ht1
    have hrnn : (0 : ℝ) ≤ t ^ (-(2⁻¹ : ℝ) - 1) := Real.rpow_nonneg ht0.le _
    calc t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t
        ≤ t ^ (-(2⁻¹ : ℝ) - 1) * (Real.log 4 * t + 2 * Real.sqrt t * Real.log t) :=
          mul_le_mul_of_nonneg_left hψ hrnn
      _ = g t := by
          rw [hg]
          have e1 : t ^ (-(2⁻¹ : ℝ) - 1) * t = t ^ (-(2⁻¹ : ℝ)) := by
            rw [← Real.rpow_add_one ht0.ne']
            ring_nf
          have e2 : t ^ (-(2⁻¹ : ℝ) - 1) * Real.sqrt t = t⁻¹ := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht0, ← Real.rpow_neg_one t]
            norm_num
          calc t ^ (-(2⁻¹ : ℝ) - 1) * (Real.log 4 * t + 2 * Real.sqrt t * Real.log t)
              = Real.log 4 * (t ^ (-(2⁻¹ : ℝ) - 1) * t)
                + 2 * ((t ^ (-(2⁻¹ : ℝ) - 1) * Real.sqrt t) * Real.log t) := by ring
            _ = Real.log 4 * t ^ (-(2⁻¹ : ℝ)) + 2 * (Real.log t * t⁻¹) := by
                rw [e1, e2]; ring
  -- step 2: integrability of both sides on Ioc 1 x
  have hint_g : IntegrableOn g (Set.Ioc 1 x) :=
    (hcont_g.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hmeas_f : AEStronglyMeasurable (fun t : ℝ => t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t)
      (volume.restrict (Set.Ioc 1 x)) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (ContinuousOn.aestronglyMeasurable (fun t ht =>
        (Real.continuousAt_rpow_const t _
          (Or.inl (by nlinarith [(Set.mem_Ioc.mp ht).1] : t ≠ 0))).continuousWithinAt)
        measurableSet_Ioc)
    · exact (Chebyshev.psi_mono.measurable.aestronglyMeasurable).restrict
  have hint_f : IntegrableOn (fun t : ℝ => t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t)
      (Set.Ioc 1 x) := by
    refine Integrable.mono' (g := fun _ => (Real.log 4 + 4) * x)
      (integrableOn_const (by simp)) hmeas_f ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht1 : (1 : ℝ) ≤ t := ht.1.le
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
    have h1 : t ^ (-(2⁻¹ : ℝ) - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num)
    have h2 : (0 : ℝ) ≤ Chebyshev.psi t := Chebyshev.psi_nonneg t
    have h3 : Chebyshev.psi t ≤ (Real.log 4 + 4) * x :=
      le_trans (Chebyshev.psi_mono ht.2) (Chebyshev.psi_le_const_mul_self hx0.le)
    have hrnn : (0 : ℝ) ≤ t ^ (-(2⁻¹ : ℝ) - 1) := Real.rpow_nonneg ht0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hrnn h2)]
    calc t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t ≤ 1 * Chebyshev.psi t :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = Chebyshev.psi t := one_mul _
      _ ≤ (Real.log 4 + 4) * x := h3
  -- step 3: compare, then evaluate ∫ g
  refine le_trans (setIntegral_mono_on hint_f hint_g measurableSet_Ioc hpoint) ?_
  rw [← intervalIntegral.integral_of_le hx]
  have hi1 : IntervalIntegrable (fun t : ℝ => Real.log 4 * t ^ (-(2⁻¹ : ℝ))) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    exact continuousOn_const.mul fun t ht =>
      (Real.continuousAt_rpow_const t _
        (Or.inl (by nlinarith [ht.1] : t ≠ 0))).continuousWithinAt
  have hi2 : IntervalIntegrable (fun t : ℝ => 2 * (Real.log t * t⁻¹)) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    refine continuousOn_const.mul (ContinuousOn.mul ?_ ?_)
    · exact fun t ht => (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
    · exact continuousOn_inv₀.mono fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        nlinarith [ht.1]
  rw [hg]
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have hv1 : ∫ t in (1:ℝ)..x, t ^ (-(2⁻¹ : ℝ)) = 2 * Real.sqrt x - 2 := by
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(2⁻¹)))]
    rw [Real.one_rpow]
    rw [Real.sqrt_eq_rpow]
    norm_num
    ring
  have hv2 : ∫ t in (1:ℝ)..x, Real.log t * t⁻¹ = Real.log x ^ 2 / 2 := by
    have hftc : ∀ t ∈ Set.uIcc (1:ℝ) x,
        HasDerivAt (fun t : ℝ => Real.log t ^ 2 / 2) (Real.log t * t⁻¹) t := by
      intro t ht
      rw [Set.uIcc_of_le hx] at ht
      have ht0 : t ≠ 0 := by nlinarith [ht.1]
      have h := ((Real.hasDerivAt_log ht0).pow 2).div_const 2
      have heq : Real.log t * t⁻¹ = ((2 : ℕ) : ℝ) * Real.log t ^ (2 - 1) * t⁻¹ / 2 := by
        push_cast
        ring
      rw [heq]
      exact h
    have hint : IntervalIntegrable (fun t : ℝ => Real.log t * t⁻¹) volume 1 x := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hx]
      refine ContinuousOn.mul ?_ ?_
      · exact fun t ht => (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
      · exact continuousOn_inv₀.mono fun t ht => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          nlinarith [ht.1]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hftc hint]
    simp [Real.log_one]
  rw [hv1, hv2]
  ring_nf
  nlinarith [Real.sqrt_nonneg x, Real.log_nonneg hx]

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

theorem solution {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n
      ≤ 2 * Real.log 4 * Real.sqrt x + 2 * Real.log x + Real.log x ^ 2 / 2 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  rw [abel_sqrt hx]
  have h1 : x ^ (-(2⁻¹ : ℝ)) * Chebyshev.psi x
      ≤ Real.log 4 * Real.sqrt x + 2 * Real.log x := by
    have hψ := Chebyshev.psi_le hx
    have hnn : (0 : ℝ) ≤ x ^ (-(2⁻¹ : ℝ)) := Real.rpow_nonneg hx0.le _
    have e1 : x ^ (-(2⁻¹ : ℝ)) * x = Real.sqrt x := by
      rw [← Real.rpow_add_one hx0.ne', Real.sqrt_eq_rpow]; norm_num
    have e2 : x ^ (-(2⁻¹ : ℝ)) * Real.sqrt x = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]; norm_num
    calc x ^ (-(2⁻¹ : ℝ)) * Chebyshev.psi x
        ≤ x ^ (-(2⁻¹ : ℝ)) * (Real.log 4 * x + 2 * Real.sqrt x * Real.log x) :=
          mul_le_mul_of_nonneg_left hψ hnn
      _ = Real.log 4 * (x ^ (-(2⁻¹ : ℝ)) * x)
          + 2 * (x ^ (-(2⁻¹ : ℝ)) * Real.sqrt x) * Real.log x := by ring
      _ = Real.log 4 * Real.sqrt x + 2 * Real.log x := by rw [e1, e2]; ring
  have h2 := integral_tail_bound hx
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  nlinarith [h1, h2]
