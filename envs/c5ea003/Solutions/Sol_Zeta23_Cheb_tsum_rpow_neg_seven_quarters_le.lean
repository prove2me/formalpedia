-- Prove2me | solution 1 for Zeta23.Cheb.tsum_rpow_neg_seven_quarters_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:14:05.234392+00:00
-- url     : https://prove2.me/submissions/a52ae2b1-ed31-4861-816a-b284548e7b51

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
import Theorems.Thm_Zeta23_Cheb_sum_range_rpow_inv_le

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
open MeasureTheory

theorem solution :
    ∑' m : ℕ, ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹ ≤ 3 := by
  refine tsum_le_of_sum_range_le (fun n => by positivity) fun N => ?_
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rcases Nat.eq_zero_or_pos M with h0 | hM
    · subst h0
      norm_num [Finset.sum_range_succ]
    · refine le_trans (sum_range_rpow_inv_le hM) ?_
      have : 0 < Real.sqrt M := Real.sqrt_pos.mpr (by exact_mod_cast hM)
      have h2 : 0 < 2 / Real.sqrt M := by positivity
      linarith
