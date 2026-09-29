-- Prove2me | Theorems.Thm_closed_unit_sublevel_gap_of_collinear_monic
-- name    : closed_unit_sublevel_gap_of_collinear_monic
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:27:32.888999+00:00
-- url     : https://prove2.me/theorems/68a7302b-c38b-47cd-a235-fca8d8c67bdf
-- title:
--   A closed unit sublevel segment from the sharp collinear bound
-- statement:
--   Let f be a monic complex polynomial of degree n at least two with all roots on one affine line. The published sharp collinear diameter theorem selects an indexed root factorization and a segment between two indexed roots on which the norm of f is at most the sharp bound C_n(D/2)^n. Whenever that bound is at most one, the same segment lies in the closed unit sublevel set of f. Distinct root indices are asserted; their coordinates may coincide when roots repeat.
-- source:
--   Independent public-entry first-use derivation from Will Cook, Erdős #1041 sharp collinear root-diameter theorem, https://prove2.me/theorems/d6293174-278a-4d7f-b89b-1f95cb82ba37 ; reader report work/prove2me_release_20260923/consumers/1041/blind_first_use_20260924/report.md

import Mathlib
open Polynomial Finset Set

theorem closed_unit_sublevel_gap_of_collinear_monic
    {n : ℕ} (hn : 2 ≤ n) (f : ℂ[X])
    (hf : f.IsMonicOfDegree n) (base dir : ℂ) (hdir : ‖dir‖ = 1)
    (hcol : ∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ)) :
    ∃ y : Fin n → ℝ, f = (∏ k, (X - C (base + dir * (y k : ℂ)))) ∧
      ∀ D : ℝ, IsGreatest {d : ℝ | ∃ j k : Fin n,
          d = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))} D →
        1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n)
            * (D / 2) ^ n ≤ 1 →
        ∃ j k : Fin n, j ≠ k ∧ y j ≤ y k ∧
          (∀ l : Fin n, y l ≤ y j ∨ y k ≤ y l) ∧
          dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) ≤ D ∧
          ∀ z ∈ segment ℝ (base + dir * (y j : ℂ))
              (base + dir * (y k : ℂ)),
            ‖f.eval z‖ ≤ 1 := by sorry
