-- Prove2me | Theorems.Thm_avram_bv_finite_times_eventually_separated
-- name    : avram_bv_finite_times_eventually_separated
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:42:37.332194+00:00
-- url     : https://prove2.me/theorems/8bb94631-5264-4984-aee3-414770f1d77a
-- title:
--   Eventually separated finite claim times on a vanishing physical grid
-- statement:
--   For a finite collection of event times and a sequence of mesh sizes converging to zero, eventually the mesh size is strictly smaller than the distance between every pair of distinct event times. This is a deterministic ingredient for separating finite-activity insurance claim jumps in a bounded-variation physical-grid argument.

import Mathlib

theorem avram_bv_finite_times_eventually_separated
    (s : Finset ℝ) (mesh : ℕ → ℝ)
    (hmesh : Filter.Tendsto mesh Filter.atTop (nhds (0 : ℝ))) :
    ∀ᶠ n in Filter.atTop, ∀ a ∈ s, ∀ b ∈ s,
      a ≠ b → mesh n < |a - b| := by sorry
