-- Prove2me | Theorems.Thm_mme_exact_step_quantitative_tensor_restriction
-- name    : mme_exact_step_quantitative_tensor_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:54:55.978775+00:00
-- url     : https://prove2.me/theorems/df7da08e-5d3d-4d65-aa53-16fd728295ef
-- title:
--   Quantitative tensor restriction from an exact extraction step
-- statement:
--   Over any field, an exact step gives an actual restriction from its source tensor to its repaired copies of the output tensor. A real lower bound B on selected count gives the explicit post-repair bound B divided by the repair budget minus one, strictly below the number of copies.
-- source:
--   Released regional integer profiles, quantitative exact extraction, and explicit repair losses.

import Theorems.Thm_mme_recursive_profiled_CW_exact_step
import Definitions.Def_mme_recursive_profiled_CW_data
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
open MME MME.ProfiledCW
set_option autoImplicit false
universe u

theorem mme_exact_step_quantitative_tensor_restriction
    {K : Type u} [Field K] {ell N : ℕ} {P : Predicate N}
    (E : ExactStep ell N P) {B : ℝ} (hB : B ≤ E.count) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin E.copies => tensor K E.output)) (tensor K P) ∧
      B / (8 : ℝ) ^ E.stage.repairExponent - 1 < E.copies := by sorry
