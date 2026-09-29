-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR10.abs_log_one_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:55:50.243775+00:00
-- url     : https://prove2.me/submissions/057f5a49-0dea-4f38-bea6-d1bd419152d2

import Definitions.Def_ErdosProblems_Erdos1049_QProductBoundsR10
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Positive q-products and q-binomial ratio coefficients

The infinite product is constructed from an absolutely
convergent logarithmic series, and is proved to be the limit of its finite
products. Its positivity is therefore not an assumed supplier.
-/

namespace ErdosProblems.Erdos1049.PaperR10
open Filter
open scoped BigOperators Topology
end ErdosProblems.Erdos1049.PaperR10

open Filter
open scoped BigOperators Topology
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR10 in
theorem solution {u a : ℝ}
    (hu : 0 ≤ u) (hua : u ≤ a) (ha : a < 1) :
    |Real.log (1 - u)| ≤ u / (1 - a) := by
  have hau : u < 1 := hua.trans_lt ha
  have hd : 0 < 1 - u := sub_pos.mpr hau
  have hda : 0 < 1 - a := sub_pos.mpr ha
  have hlog : Real.log (1 - u) ≤ 0 := by
    have hh := Real.log_le_log hd (by linarith : 1 - u ≤ 1)
    simpa using hh
  have hl := Real.one_sub_inv_le_log_of_pos hd
  have hid : 1 - (1 - u)⁻¹ = -(u / (1 - u)) := by
    field_simp [hd.ne']
    <;> ring
  rw [hid] at hl
  have hdiv : u / (1 - u) ≤ u / (1 - a) :=
    div_le_div_of_nonneg_left hu hda (by linarith)
  rw [abs_of_nonpos hlog]
  linarith
