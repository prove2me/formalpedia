-- Prove2me | solution 1 for Zeta23.Tail.two_sides_numeric
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:01:20.505011+00:00
-- url     : https://prove2.me/submissions/9d8ec580-c9c8-4c91-8111-9afe0621ccbd

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Zeta23_Tail_Basic

-- from Zeta23.Tail.Count
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/Count.lean — the zero-count sum in the proof of [prop:tail] (the paper §4.2).


Paper, verbatim: "It remains to bound ∑_{γ∉I'} m_ρ D⁻³ (zeros counted with multiplicity).
Zeros with γ > 2T+D₀: grouping them into γ ∈ (2T+D₀+j, 2T+D₀+j+1], j ≥ 0, this part is at
most ∑_{j≥0} A₀ log(2T+D₀+j+4)(D₀+j)⁻³ ≤ (3/2)A₀ log(4T) D₀⁻² for T large (split at j = T
and use D₀ ≥ 2). Zeros with 0 < γ < T−D₀ contribute likewise at most (3/2)A₀ log(4T)D₀⁻²,
and zeros with γ ≤ 0 have D ≥ T and contribute at most ∑_{j≥0} A₀ log(j+4)(T+j)⁻³
≪ T⁻² log T. Altogether ∑_{γ∉I'} m_ρ D⁻³ ≤ 4A₀ log(4T) D₀⁻² for T ≥ T₀."

We prove the bound for every FINITE sub-family of tail zeros (which yields both the
summability and the bound for the full series downstream), with the explicit absolute
threshold T₀ of Zeta23/Tail/Basic.lean. Only the final constant 4 is load-bearing (it is
the 4 in θ₀); we do not follow the paper's intermediate 3/2 + 3/2 + o(1) split. Our
grouping: unit windows indexed by the integer distance j from the nearer endpoint of
I = [T,2T] (lower side: T−j−1 < γ ≤ T−j, which also covers ALL γ ≤ 0; upper side:
2T+j < γ ≤ 2T+j+1), each window weighted by max(D₀, j)⁻³ and counted by the two-sided
local count ≤ A₀ log(2T+4+j); integrals are replaced by telescoping sums.
-/

noncomputable section

open Finset Real

namespace Zeta23
namespace Tail

/-! #### Telescoping sums replacing ∫ x⁻³ and ∫ x⁻² -/








/-! #### Summing the window weights -/


/-! #### One side of the tail, abstractly -/


/-! #### Numerics at T ≥ T₀ -/

lemma one_le_log_four_mul {T : ℝ} (hT : T₀ ≤ T) : 1 ≤ Real.log (4 * T) := by
  have hT' : (300 : ℝ) ≤ T := hT
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith


/-! #### The zero-count sum -/


/-! #### The boundary count N(I' ∖ I) -/



end Tail
end Zeta23
end
open Finset Real
open Zeta23
open Tail

theorem solution {T : ℝ} (hT : T₀ ≤ T) :
    2 * ((2 * (Real.sqrt T ^ 3)⁻¹ + (Real.sqrt T ^ 2)⁻¹ / 2) * Real.log (2 * T + 4)
          + (2 * (Real.sqrt T ^ 2)⁻¹ + (Real.sqrt T)⁻¹) / (2 * T + 4))
      ≤ 4 * Real.log (4 * T) / T := by
  have hT' : (300 : ℝ) ≤ T := hT
  set u := Real.sqrt T with hu
  have hu2 : u ^ 2 = T := Real.sq_sqrt (by linarith)
  have hu17 : 17 ≤ u := by
    rw [hu, Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hu0 : 0 < u := by linarith
  set ℓ := Real.log (4 * T) with hℓ
  have hℓ1 : 1 ≤ ℓ := one_le_log_four_mul hT
  have hℓ' : Real.log (2 * T + 4) ≤ ℓ :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog_nn : 0 ≤ Real.log (2 * T + 4) := Real.log_nonneg (by linarith)
  rw [← hu2] at hℓ' ⊢
  -- replace log(2T+4) by ℓ and 2T+4 by 2T in the denominator
  have step1 : (2 * (u ^ 3)⁻¹ + (u ^ 2)⁻¹ / 2) * Real.log (2 * u ^ 2 + 4)
      ≤ (2 * (u ^ 3)⁻¹ + (u ^ 2)⁻¹ / 2) * ℓ :=
    mul_le_mul_of_nonneg_left hℓ' (by positivity)
  have step2 : (2 * (u ^ 2)⁻¹ + u⁻¹) / (2 * u ^ 2 + 4) ≤ (2 * (u ^ 2)⁻¹ + u⁻¹) / (2 * u ^ 2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have step3 : 2 * ((2 * (u ^ 3)⁻¹ + (u ^ 2)⁻¹ / 2) * ℓ + (2 * (u ^ 2)⁻¹ + u⁻¹) / (2 * u ^ 2))
      ≤ 4 * ℓ / u ^ 2 := by
    rw [← sub_nonneg]
    have key : 4 * ℓ / u ^ 2
        - 2 * ((2 * (u ^ 3)⁻¹ + (u ^ 2)⁻¹ / 2) * ℓ + (2 * (u ^ 2)⁻¹ + u⁻¹) / (2 * u ^ 2))
        = (ℓ * (3 * u ^ 2 - 4 * u) - 2 - u) / u ^ 4 := by
      field_simp
      ring
    rw [key]
    apply div_nonneg _ (by positivity)
    have h34 : 0 ≤ 3 * u ^ 2 - 4 * u := by nlinarith
    have := mul_le_mul_of_nonneg_right hℓ1 h34
    nlinarith
  linarith
