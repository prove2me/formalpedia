-- Prove2me | solution 1 for Zeta23.Cheb.rpow_inv_le_telescope
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:15:44.301673+00:00
-- url     : https://prove2.me/submissions/a893574b-76d4-4e81-a4a1-2601f97aab98

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
open Finset Real Chebyshev
open ArithmeticFunction hiding log
open scoped Nat.Prime
open MeasureTheory

theorem solution {m : ℕ} (hm : 2 ≤ m) :
    ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹ ≤ 2 * (1 / Real.sqrt (m - 1) - 1 / Real.sqrt m) := by
  have hm1 : (1:ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.one_le_of_lt hm
  have hm0 : (0:ℝ) < m := by linarith
  have hm2 : (2:ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm10 : (0:ℝ) < (m : ℝ) - 1 := by linarith
  have hs : 0 < Real.sqrt ((m:ℝ) - 1) := Real.sqrt_pos.mpr hm10
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hmono : Real.sqrt ((m:ℝ) - 1) ≤ Real.sqrt m := Real.sqrt_le_sqrt (by linarith)
  have h1 : Real.sqrt m * Real.sqrt m = (m:ℝ) := Real.mul_self_sqrt hm0.le
  have h2 : Real.sqrt ((m:ℝ) - 1) * Real.sqrt ((m:ℝ) - 1) = (m:ℝ) - 1 := Real.mul_self_sqrt hm10.le
  have hprod : (Real.sqrt m - Real.sqrt ((m:ℝ) - 1)) * (Real.sqrt m + Real.sqrt ((m:ℝ) - 1)) = 1 := by
    nlinarith [h1, h2]
  have hdiff : 1 / Real.sqrt ((m:ℝ) - 1) - 1 / Real.sqrt m
      = 1 / (Real.sqrt ((m:ℝ) - 1) * Real.sqrt m * (Real.sqrt m + Real.sqrt ((m:ℝ) - 1))) := by
    rw [div_sub_div _ _ hs.ne' hsm.ne', one_mul, mul_one]
    rw [show Real.sqrt m - Real.sqrt ((m:ℝ) - 1)
        = 1 / (Real.sqrt m + Real.sqrt ((m:ℝ) - 1)) from by
      rw [eq_div_iff (by positivity)]
      exact hprod]
    rw [div_div]
    ring_nf
  have hsq : Real.sqrt m = (m:ℝ) ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow m
  have h32 : (m:ℝ) ^ ((3:ℝ)/2) = (m:ℝ) ^ ((1:ℝ)/2) * (m:ℝ) ^ ((1:ℝ)/2) * (m:ℝ) ^ ((1:ℝ)/2) := by
    rw [← Real.rpow_add hm0, ← Real.rpow_add hm0]
    norm_num
  have hden : Real.sqrt ((m:ℝ) - 1) * Real.sqrt m * (Real.sqrt m + Real.sqrt ((m:ℝ) - 1))
      ≤ 2 * (m:ℝ) ^ ((3:ℝ)/2) := by
    calc Real.sqrt ((m:ℝ) - 1) * Real.sqrt m * (Real.sqrt m + Real.sqrt ((m:ℝ) - 1))
        ≤ Real.sqrt m * Real.sqrt m * (2 * Real.sqrt m) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hmono hsm.le) (by linarith)
            (by positivity) (by positivity)
      _ = 2 * ((m:ℝ) ^ ((1:ℝ)/2) * (m:ℝ) ^ ((1:ℝ)/2) * (m:ℝ) ^ ((1:ℝ)/2)) := by
          rw [hsq]
          ring
      _ = 2 * (m:ℝ) ^ ((3:ℝ)/2) := by rw [h32]
  have h74 : (m:ℝ) ^ ((3:ℝ)/2) ≤ (m:ℝ) ^ ((7:ℝ)/4) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  rw [hdiff]
  calc ((m:ℝ) ^ ((7:ℝ)/4))⁻¹ = 1 / ((m:ℝ) ^ ((7:ℝ)/4)) := (one_div _).symm
    _ ≤ 1 / ((m:ℝ) ^ ((3:ℝ)/2)) := one_div_le_one_div_of_le (by positivity) h74
    _ = 2 * (1 / (2 * (m:ℝ) ^ ((3:ℝ)/2))) := by
        field_simp
    _ ≤ 2 * (1 / (Real.sqrt ((m:ℝ) - 1) * Real.sqrt m * (Real.sqrt m + Real.sqrt ((m:ℝ) - 1)))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact one_div_le_one_div_of_le (by positivity) hden
