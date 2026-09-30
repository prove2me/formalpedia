-- Prove2me | Theorems.Thm_Hirsch_box_slice_diameter_le_dimension
-- name    : Hirsch.box_slice_diameter_le_dimension
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-08T14:39:23.919912+00:00
-- url     : https://prove2.me/theorems/76900e5f-9732-427a-b648-9499518dce05
-- title:
--   A box cut by one balance equation has graph diameter at most the number of coordinates
-- statement:
--   For any real capacities cap indexed by Fin d and any real total, the set of x with 0 <= x_k <= cap_k and sum x_k = total has vertex-edge graph diameter at most d. Negative capacities simply make it empty; zero-width coordinates and dimension zero are included. The proof constructs maximal two-coordinate edges with a strictly decreasing mismatch-plus-mixed-buffer potential. This is a restricted one-balance box theorem, not a general polynomial Hirsch bound.
-- source:
--   Constructive formalization in jjoshua2/prove2me-work, chatgpt/box-slice-pivot. Related two-row transportation bounds are known; no literature-priority claim.

import Mathlib
import Definitions.Def_Hirsch_model
open Set Hirsch

theorem Hirsch.box_slice_diameter_le_dimension (d : ℕ) (cap : Fin d → ℝ) (total : ℝ) :
    DiamLE {x : Fin d → ℝ | (∀ k, 0 ≤ x k ∧ x k ≤ cap k) ∧ ∑ k, x k = total} d  := by sorry
