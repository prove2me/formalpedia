-- Prove2me | solution 1 for lean_workbook_plus_52051
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:27:11.195462+00:00
-- url     : https://prove2.me/submissions/511803b3-ee1e-4f4c-9770-6cd9c4b0ab65

import Mathlib.Analysis.Complex.Basic

theorem solution (g : ℝ → ℝ) : ∃ h k : ℝ → ℝ, Even h ∧ Odd k ∧ g = h + k := by
  refine ⟨fun x => (g x + g (-x)) / 2, fun x => (g x - g (-x)) / 2, ?_, ?_, ?_⟩
  · -- `Even h` in the additive monoid `ℝ → ℝ`: `h = r + r` with `r = h / 2`
    refine ⟨fun x => (g x + g (-x)) / 4, ?_⟩
    funext x
    simp only [Pi.add_apply]
    ring
  · -- `Odd k` in the semiring `ℝ → ℝ`: `k = 2 * m + 1` with `m = (k - 1) / 2`
    refine ⟨fun x => ((g x - g (-x)) / 2 - 1) / 2, ?_⟩
    funext x
    simp only [Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply]
    ring
  · funext x
    simp only [Pi.add_apply]
    ring
