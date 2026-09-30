-- Prove2me | solution 1 for RybinAI2026.P01.aligned_diagonal_pair_contraction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T04:13:50.491694+00:00
-- url     : https://prove2.me/submissions/c994551a-e90b-4e02-91cc-06ec1a8be38a

import Mathlib
import Theorems.Thm_RybinAI2026_P01_psi_fractional_order_properties
import Theorems.Thm_RybinAI2026_P01_diagonal_pair_low_ratio_bounds
import Theorems.Thm_RybinAI2026_P01_diagonal_pair_high_ratio_bounds
import Theorems.Thm_RybinAI2026_P01_diagonal_pair_G_ratio_identity
import Theorems.Thm_RybinAI2026_P01_diagonal_pair_contraction_from_envelopes

open MeasureTheory

theorem solution (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    let ψ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹
    let r₁ : ℝ := a / (a + c) * (ψ ((b + d) / (a + c)) / ψ (b / a))
    let r₂ : ℝ := d / (b + d) * (ψ ((a + c) / (b + d)) / ψ (c / d))
    r₁ ^ 2 + r₂ ^ 2 ≤ 1 := by
  let ψ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1, (1 + (t - 1) * s ^ 2)⁻¹
  let G : ℝ → ℝ := fun t => Real.sqrt t * ψ t
  let x : ℝ := a / (a + c)
  let y : ℝ := d / (b + d)
  let T : ℝ := (b + d) / (a + c)
  let α : ℝ := x / (1 - y)
  let β : ℝ := y / (1 - x)
  let A : ℝ := Real.sqrt (x * (1 - y))
  let B : ℝ := Real.sqrt (y * (1 - x))
  let z : ℝ := Real.sqrt T
  let r : ℝ := A * (G T / G (T / α))
  let s : ℝ := B * (G (1 / T) / G (1 / (β * T)))
  have hac : 0 < a + c := add_pos ha hc
  have hbd : 0 < b + d := add_pos hb hd
  have hx : 0 < x := div_pos ha hac
  have hy : 0 < y := div_pos hd hbd
  have hx1 : x < 1 := by
    dsimp [x]
    exact (div_lt_iff₀ hac).2 (by linarith)
  have hy1 : y < 1 := by
    dsimp [y]
    exact (div_lt_iff₀ hbd).2 (by linarith)
  have hT : 0 < T := div_pos hbd hac
  have hα : 0 < α := div_pos hx (sub_pos.mpr hy1)
  have hβ : 0 < β := div_pos hy (sub_pos.mpr hx1)
  have hTa : 0 < T / α := div_pos hT hα
  have h1T : 0 < 1 / T := one_div_pos.mpr hT
  have hβT : 0 < β * T := mul_pos hβ hT
  have h1βT : 0 < 1 / (β * T) := one_div_pos.mpr hβT
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hA : A ^ 2 = x * (1 - y) := Real.sq_sqrt (le_of_lt (mul_pos hx (sub_pos.mpr hy1)))
  have hB : B ^ 2 = y * (1 - x) := Real.sq_sqrt (le_of_lt (mul_pos hy (sub_pos.mpr hx1)))
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  rcases RybinAI2026.P01.psi_fractional_order_properties with ⟨hGpos, hGmono, hGanti⟩
  have hr0 : 0 ≤ r :=
    mul_nonneg hA0 (div_nonneg (le_of_lt (hGpos T hT)) (le_of_lt (hGpos _ hTa)))
  have hs0 : 0 ≤ s :=
    mul_nonneg hB0 (div_nonneg (le_of_lt (hGpos _ h1T)) (le_of_lt (hGpos _ h1βT)))
  have hlow : x + y ≤ 1 → r ^ 2 ≤ A ^ 2 ∧ s ^ 2 ≤ B ^ 2 := by
    intro hxy
    have hh := RybinAI2026.P01.diagonal_pair_low_ratio_bounds G hGpos hGmono
      x y T hx hx1 hy hy1 hT hxy
    have hrle : r ^ 2 ≤ x * (1 - y) := by
      simpa [r, A, α] using hh.1
    have hsle : s ^ 2 ≤ y * (1 - x) := by
      simpa [s, B, β] using hh.2
    exact ⟨hrle.trans_eq hA.symm, hsle.trans_eq hB.symm⟩
  have hhigh : 1 < x + y →
      r ≤ (x + A * z) / (1 + z) ∧ s ≤ (B + y * z) / (1 + z) := by
    intro hxy
    simpa [r, s, A, B, α, β, z] using
      RybinAI2026.P01.diagonal_pair_high_ratio_bounds G hGpos hGanti
        x y T hx hx1 hy hy1 hT hxy
  have hbound := RybinAI2026.P01.diagonal_pair_contraction_from_envelopes
    hx.le (le_of_lt hx1) hy.le (le_of_lt hy1) hA0 hB0 hA hB hz hr0 hs0 hlow hhigh
  have hids := RybinAI2026.P01.diagonal_pair_G_ratio_identity a b c d ha hb hc hd
  rcases hids with ⟨hfirst, hsecond⟩
  change x * (ψ T / ψ (b / a)) = r at hfirst
  change y * (ψ (1 / T) / ψ (c / d)) = s at hsecond
  have hTinv : 1 / T = (a + c) / (b + d) := by
    dsimp [T]
    field_simp [hac.ne', hbd.ne']
  rw [hTinv] at hsecond
  change (x * (ψ T / ψ (b / a))) ^ 2 +
      (y * (ψ ((a + c) / (b + d)) / ψ (c / d))) ^ 2 ≤ 1
  rw [hfirst, hsecond]
  exact hbound
