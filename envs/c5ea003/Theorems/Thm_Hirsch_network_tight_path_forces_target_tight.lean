-- Prove2me | Theorems.Thm_Hirsch_network_tight_path_forces_target_tight
-- name    : Hirsch.network_tight_path_forces_target_tight
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T20:24:47.398371+00:00
-- url     : https://prove2.me/theorems/828317c1-80e8-4709-bc40-60a3d0f5c79b
-- title:
--   A tight difference-constraint path must saturate a target inequality saturated by another feasible path
-- statement:
--   Suppose u saturates every consecutive difference constraint along a directed path, v satisfies all the same path constraints, v saturates a shortcut/target inequality with bound C, and u satisfies that target inequality. Then u must also saturate the target inequality. This is the scalar core used in the network-potential routing argument to force a backward tight row during target insertion.
-- source:
--   Standalone Mathlib-only restatement of the target-tightness primitive developed in PR #210.

import Mathlib
set_option autoImplicit false
noncomputable section

theorem Hirsch.network_tight_path_forces_target_tight
    (n : ℕ) (u v : ℕ → ℝ) (cost : Fin n → ℝ) (C : ℝ)
    (hu : ∀ i : Fin n, u (i.val + 1) - u i.val = cost i)
    (hv : ∀ i : Fin n, v (i.val + 1) - v i.val ≤ cost i)
    (hvtarget : v n - v 0 = C)
    (hutarget : u n - u 0 ≤ C) :
    u n - u 0 = C := by sorry
