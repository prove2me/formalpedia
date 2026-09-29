-- Prove2me | solution 1 for Zeta23.Tail.boundary_count_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:10:06.320358+00:00
-- url     : https://prove2.me/submissions/02b1ca9f-f2ed-45ad-af7f-6b49945ca384

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Zeta23_Tail_Basic

-- from Zeta23.Tail.Basic
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/Basic.lean — shared elementary definitions for prop:tail (the paper §4.2).
-/

noncomputable section

namespace Zeta23
namespace Tail











lemma LocalCount.A₀_pos {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A₀ : ℝ}
    (h : LocalCount γ m A₀) : 0 < A₀ := lt_of_lt_of_le one_pos h.one_le

end Tail
end Zeta23
end
end

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

/-- Counting by unit windows: if every zero of s falls in one of K windows (key < K) and each
window holds total multiplicity ≤ C, then ∑_s m ≤ K·C. -/
lemma sum_mult_le_of_windows {ι : Type*} (s : Finset ι) (m : ι → ℕ) (key : ι → ℕ) (K : ℕ)
    {C : ℝ} (hkey : ∀ ρ ∈ s, key ρ < K)
    (hcount : ∀ j < K, ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ) ≤ C) :
    ∑ ρ ∈ s, (m ρ : ℝ) ≤ K * C := by
  rw [← sum_fiberwise_of_maps_to (g := key) (t := range K)
    (fun ρ hρ => mem_range.mpr (hkey ρ hρ))]
  calc ∑ j ∈ range K, ∑ ρ ∈ s with key ρ = j, (m ρ : ℝ)
      ≤ ∑ j ∈ range K, C := sum_le_sum fun j hj => hcount j (mem_range.mp hj)
    _ = K * C := by rw [sum_const, card_range, nsmul_eq_mul]


end Tail
end Zeta23
end
open Finset Real
open Zeta23
open Tail

theorem solution {ι : Type*} {γ : ι → ℝ} {m : ι → ℕ} {A₀ T : ℝ}
    (hN : LocalCount γ m A₀) (hT : T₀ ≤ T) (s : Finset ι)
    (hs : ∀ ρ ∈ s, (T - Real.sqrt T < γ ρ ∧ γ ρ ≤ T)
      ∨ (2 * T < γ ρ ∧ γ ρ ≤ 2 * T + Real.sqrt T)) :
    ∑ ρ ∈ s, (m ρ : ℝ) ≤ 3 * A₀ * Real.sqrt T * Real.log (4 * T) := by
  classical
  have hT' : (300 : ℝ) ≤ T := hT
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hA₀ : 0 ≤ A₀ := hN.A₀_pos.le
  set D₀ := Real.sqrt T with hD₀def
  have hD₀ : 17 ≤ D₀ := by
    rw [hD₀def, Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hD₀T : D₀ ^ 2 = T := Real.sq_sqrt hT0
  have hD₀leT : D₀ + 4 ≤ T := by nlinarith
  set K : ℕ := ⌈D₀⌉₊ with hK
  have hKlt : (K : ℝ) < D₀ + 1 := Nat.ceil_lt_add_one (by linarith)
  have hKge : D₀ ≤ K := Nat.le_ceil D₀
  set C : ℝ := A₀ * Real.log (4 * T) with hCdef
  have hlog1 : 1 ≤ Real.log (4 * T) := one_le_log_four_mul hT
  have hC : 0 ≤ C := by positivity
  have hlogmono : ∀ (t : ℝ), |t| + 3 ≤ 4 * T →
      A₀ * Real.log (|t| + 3) ≤ C := fun t h =>
    mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) h) hA₀
  set slo := s.filter (fun ρ => γ ρ ≤ T) with hslo
  set shi := s.filter (fun ρ => ¬ γ ρ ≤ T) with hshi
  have hlo_mem : ∀ ρ ∈ slo, T - D₀ < γ ρ ∧ γ ρ ≤ T := by
    intro ρ hρ
    rw [hslo, mem_filter] at hρ
    rcases hs ρ hρ.1 with h | h
    · exact h
    · exact absurd hρ.2 (by linarith [h.1])
  have hhi_mem : ∀ ρ ∈ shi, 2 * T < γ ρ ∧ γ ρ ≤ 2 * T + D₀ := by
    intro ρ hρ
    rw [hshi, mem_filter] at hρ
    rcases hs ρ hρ.1 with h | h
    · exact absurd h.2 hρ.2
    · exact h
  -- lower boundary strip: key = ⌊T − γ⌋₊ < K
  have hlo : ∑ ρ ∈ slo, (m ρ : ℝ) ≤ K * C := by
    apply sum_mult_le_of_windows slo m (fun ρ => ⌊T - γ ρ⌋₊) K
    · intro ρ hρ
      have h := hlo_mem ρ hρ
      have : (⌊T - γ ρ⌋₊ : ℝ) < K :=
        lt_of_le_of_lt (Nat.floor_le (by linarith [h.2])) (by linarith [h.1])
      exact_mod_cast this
    · intro j hj
      refine (hN.window (T - j - 1) _ ?_).trans (hlogmono _ ?_)
      · intro ρ hρ
        rw [mem_filter] at hρ
        obtain ⟨hρs, hρj⟩ := hρ
        have hnn : 0 ≤ T - γ ρ := by linarith [(hlo_mem ρ hρs).2]
        have := (Nat.floor_eq_iff hnn).mp hρj
        constructor <;> linarith [this.1, this.2]
      · have hj' : (j : ℝ) < D₀ + 1 := lt_of_lt_of_le (by exact_mod_cast hj) hKlt.le
        rw [abs_of_nonneg (by linarith)]
        linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  -- upper boundary strip: key = ⌈γ − 2T⌉₊ − 1 < K
  have hhi : ∑ ρ ∈ shi, (m ρ : ℝ) ≤ K * C := by
    have hceil1 : ∀ ρ ∈ shi, 1 ≤ ⌈γ ρ - 2 * T⌉₊ := fun ρ hρ =>
      Nat.one_le_ceil_iff.mpr (by linarith [(hhi_mem ρ hρ).1])
    apply sum_mult_le_of_windows shi m (fun ρ => ⌈γ ρ - 2 * T⌉₊ - 1) K
    · intro ρ hρ
      have h := hhi_mem ρ hρ
      have : ⌈γ ρ - 2 * T⌉₊ ≤ K := by rw [hK]; exact Nat.ceil_mono (by linarith [h.2])
      have := hceil1 ρ hρ
      omega
    · intro j hj
      refine (hN.window (2 * T + j) _ ?_).trans (hlogmono _ ?_)
      · intro ρ hρ
        rw [mem_filter] at hρ
        obtain ⟨hρs, hρj⟩ := hρ
        have hc : ⌈γ ρ - 2 * T⌉₊ = j + 1 := by have := hceil1 ρ hρs; omega
        have := (Nat.ceil_eq_iff (Nat.succ_ne_zero j)).mp hc
        push_cast at this
        constructor <;> linarith [this.1, this.2]
      · have hj' : (j : ℝ) < D₀ + 1 := lt_of_lt_of_le (by exact_mod_cast hj) hKlt.le
        rw [abs_of_nonneg (by positivity)]
        linarith
  -- combine: 2·K·C ≤ 2(D₀+1)·A₀ log(4T) ≤ 3 D₀ A₀ log(4T)
  rw [← sum_filter_add_sum_filter_not s (fun ρ => γ ρ ≤ T)]
  have hK' : (K : ℝ) * C ≤ (D₀ + 1) * C := mul_le_mul_of_nonneg_right hKlt.le hC
  have : (2 : ℝ) * ((D₀ + 1) * C) ≤ 3 * A₀ * D₀ * Real.log (4 * T) := by
    rw [hCdef]
    have : 2 * (D₀ + 1) ≤ 3 * D₀ := by linarith
    have hAl : 0 ≤ A₀ * Real.log (4 * T) := hC
    nlinarith
  linarith
