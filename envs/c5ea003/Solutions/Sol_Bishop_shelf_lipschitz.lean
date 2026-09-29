-- Prove2me | solution 1 for Bishop.shelf_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:39:45.646628+00:00
-- url     : https://prove2.me/submissions/6c1307de-927d-42fd-a36d-36b23049e753

-- Sol generated from Logic/ConstructiveAnalysis/BrouwerianCounterexamples.lean
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BrouwerianCounterexamples
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveIVT
/-
# A Brouwerian counterexample: the exact IVT has no continuous solution operator

This file makes precise the sense in which the *exact* intermediate value theorem
fails constructively, while the approximate one (proved in
`Logic/ConstructiveAnalysis/ConstructiveIVT.lean`) holds.

We use Bishop's standard family of "shelf" functions

  `shelf t x = min (x - 1) (max t (x - 2))`,   `t ∈ [-1,1]`, `x ∈ [0,3]`.

Each `shelf t` is `1`-Lipschitz (so it has the explicit modulus of uniform
continuity `ω = id`), and satisfies `shelf t 0 ≤ 0 ≤ shelf t 3`, so the approximate
IVT applies to the whole family uniformly (`shelf_approx_root`).  Nevertheless:

* `shelf_root_of_mem_Ioo` : if `1 < x < 2` and `shelf t x = 0` then `t = 0`;
* `no_continuous_root_selector` : there is **no continuous** map `t ↦ r t` on
  `[-1,1]` with `shelf t (r t) = 0`.

Since every constructively (in particular, computably) defined map `ℝ → ℝ` is
continuous, this shows that no constructive proof of the exact IVT can exist: the
root cannot be obtained continuously — let alone computably — from the data.
The hypothesis that rescues the exact IVT in `constructive_ivt` is a positive lower
slope bound; `shelf_zero_slope_bound_nonpos` shows that this is precisely what the
family violates at `t = 0`, where `shelf 0` is constant on `[1,2]`.
-/


open Bishop

open Set














open Bishop in
theorem solution(t x y : ℝ) : |shelf t x - shelf t y| ≤ |x - y| := by
  have h1 : |shelf t x - shelf t y| ≤ max |(x - 1) - (y - 1)| |max t (x - 2) - max t (y - 2)| :=
    abs_min_sub_min_le_max _ _ _ _
  have h2 : |max t (x - 2) - max t (y - 2)| ≤ max |t - t| |(x - 2) - (y - 2)| :=
    abs_max_sub_max_le_max _ _ _ _
  have h3 : |(x - 1) - (y - 1)| = |x - y| := by ring_nf
  have h4 : |(x - 2) - (y - 2)| = |x - y| := by ring_nf
  have h5 : max |t - t| |(x - 2) - (y - 2)| = |x - y| := by
    simp
  rw [h3] at h1
  rw [h5] at h2
  exact h1.trans (max_le le_rfl h2)
