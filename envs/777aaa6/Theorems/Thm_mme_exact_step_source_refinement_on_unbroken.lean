-- Prove2me | Theorems.Thm_mme_exact_step_source_refinement_on_unbroken
-- name    : mme_exact_step_source_refinement_on_unbroken
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:43:34.658673+00:00
-- url     : https://prove2.me/theorems/5e5766ec-fa24-46bb-8ce8-cb85a5620fe4
-- title:
--   Refine extraction sources on unbroken words
-- statement:
--   An exact extraction step can be transported from source P to source Q when P implies Q on the unbroken words at every selected address. The selected count, repair exponent, number of copies, and output predicate are preserved.
-- source:
--   Exact regional extraction and complementary child grades.

import Definitions.Def_mme_recursive_profiled_CW_data

open BigOperators MME MME.ProfiledCW MME.RecursiveYZ MME.CompleteSplit
open scoped Classical
set_option autoImplicit false

theorem mme_exact_step_source_refinement_on_unbroken
    {ell N : ℕ} {P Q : Predicate N} (E : ExactStep ell N P)
    (hPQ : ∀ j i f, f ∈ unbrokenWords E.stage.total i (E.address j) (E.stage.mu i) →
      P i (flatten E.stage.positions E.length f) →
      Q i (flatten E.stage.positions E.length f)) :
    ∃ F : ExactStep ell N Q, F.count = E.count ∧
      F.stage.repairExponent = E.stage.repairExponent ∧
      F.copies = E.copies ∧ F.output = E.output := by sorry
