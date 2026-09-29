-- Prove2me | solution 1 for Zeta23.Tail.one_side_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:02:04.938527+00:00
-- url     : https://prove2.me/submissions/4c449334-7860-4e97-8c64-d504146e6c4b

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Zeta23_Tail_Basic
import Theorems.Thm_Zeta23_Tail_sum_window_weights_le

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



/-! #### The zero-count sum -/


/-! #### The boundary count N(I' ∖ I) -/



end Tail
end Zeta23
end
open Finset Real
open Zeta23
open Tail

theorem solution {ι : Type*} (s : Finset ι) (x : ι → ℝ) (m : ι → ℕ) (key : ι → ℕ)
    {A₀ B D₀ : ℝ} (hA₀ : 0 ≤ A₀) (hB : 1 ≤ B) (hD₀ : 2 ≤ D₀)
    (hx : ∀ ρ ∈ s, D₀ ≤ x ρ) (hkey_le : ∀ ρ ∈ s, (key ρ : ℝ) ≤ x ρ)
    (hkey_ge : ∀ ρ ∈ s, x ρ ≤ key ρ + 1)
    (hcount : ∀ j : ℕ, ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) ≤ A₀ * Real.log (B + j)) :
    ∑ ρ ∈ s, (m ρ : ℝ) * ((x ρ) ^ 3)⁻¹
      ≤ A₀ * ((2 * (D₀ ^ 3)⁻¹ + (D₀ ^ 2)⁻¹ / 2) * Real.log B
          + (2 * (D₀ ^ 2)⁻¹ + D₀⁻¹) / B) := by
  have hD0 : 0 < D₀ := by linarith
  rw [← sum_fiberwise_of_maps_to (g := key) (t := s.image key)
    (fun ρ hρ => mem_image_of_mem key hρ)]
  have hfiber : ∀ j ∈ s.image key,
      ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) * ((x ρ) ^ 3)⁻¹
        ≤ A₀ * (((max D₀ j) ^ 3)⁻¹ * Real.log (B + j)) := by
    intro j _
    have hM : 0 < max D₀ (j : ℝ) := lt_max_of_lt_left hD0
    calc ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) * ((x ρ) ^ 3)⁻¹
        ≤ ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) * ((max D₀ j) ^ 3)⁻¹ := by
          apply sum_le_sum
          intro ρ hρ
          simp only [mem_filter] at hρ
          obtain ⟨hρs, hρj⟩ := hρ
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          apply inv_anti₀ (pow_pos hM 3)
          apply pow_le_pow_left₀ hM.le
          refine max_le (hx ρ hρs) ?_
          have := hkey_le ρ hρs
          rw [hρj] at this
          exact this
      _ = ((max D₀ j) ^ 3)⁻¹ * ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) := by
          rw [mul_sum]
          exact sum_congr rfl fun _ _ => mul_comm _ _
      _ ≤ ((max D₀ j) ^ 3)⁻¹ * (A₀ * Real.log (B + j)) :=
          mul_le_mul_of_nonneg_left (hcount j) (by positivity)
      _ = _ := by ring
  refine (sum_le_sum hfiber).trans ?_
  rw [← mul_sum]
  apply mul_le_mul_of_nonneg_left _ hA₀
  apply sum_window_weights_le _ hB hD₀
  intro j hj
  obtain ⟨ρ, hρ, rfl⟩ := mem_image.mp hj
  exact (hx ρ hρ).trans (hkey_ge ρ hρ)
