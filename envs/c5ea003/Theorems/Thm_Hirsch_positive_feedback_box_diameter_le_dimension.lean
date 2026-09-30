-- Prove2me | Theorems.Thm_Hirsch_positive_feedback_box_diameter_le_dimension
-- name    : Hirsch.positive_feedback_box_diameter_le_dimension
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-12T22:41:46.86755+00:00
-- url     : https://prove2.me/theorems/4096cd8a-6bf6-4788-89be-e67f84f6c92f
-- title:
--   Contractive nonnegative feedback boxes have ordinary-edge diameter at most their dimension
-- statement:
--   Let C be an entrywise nonnegative real d by d matrix and b a strictly
--   positive vector. Suppose a strictly positive vector w satisfies Cw < w in
--   every coordinate. Then the ordinary-edge graph of the polytope
--   {x : 0 <= x <= b + Cx} has diameter at most d.
--
--   The proof constructs and classifies its vertices by lower/upper binary
--   signatures and proves that changing one signature coordinate gives an
--   ordinary edge. It imposes no dimension cap or acyclicity condition on C.
--   The weighted maximum principle is classical; this is its explicit
--   ordinary-edge formalization for the Hirsch workspace. This sufficient class
--   does not imply that arbitrary Hirsch carriers have this form.
-- source:
--   Classical complementary-basis and weighted maximum-principle argument, explicitly formalized at https://github.com/jjoshua2/prove2me-work/tree/9701b79441ce8ee2e935f7527ab7f01864407bff

import Mathlib
import Definitions.Def_Hirsch_model
open Set Hirsch
open scoped BigOperators

theorem Hirsch.positive_feedback_box_diameter_le_dimension {d : ℕ} (C : Fin d → Fin d → ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (b w : Fin d → ℝ) (hb : ∀ i, 0 < b i) (hw : ∀ i, 0 < w i)
    (hcw : ∀ i, (∑ j, C i j * w j) < w i) :
    DiamLE {x : Fin d → ℝ | (∀ i, 0 ≤ x i) ∧
      ∀ i, x i ≤ b i + ∑ j, C i j * x j} d := by sorry
