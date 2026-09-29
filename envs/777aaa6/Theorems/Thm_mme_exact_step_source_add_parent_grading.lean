-- Prove2me | Theorems.Thm_mme_exact_step_source_add_parent_grading
-- name    : mme_exact_step_source_add_parent_grading
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:45:18.69792+00:00
-- url     : https://prove2.me/theorems/7c1f89cd-3c3a-4a35-9027-41714ba862a0
-- title:
--   Add exact parent grading without losing extraction copies
-- statement:
--   Every exact extraction step can have its source strengthened by the prescribed parent grading at every regional position. The selected count, repair exponent, number of copies, and output predicate are preserved.
-- source:
--   Exact regional extraction and complementary child grades.

import Definitions.Def_mme_recursive_profiled_CW_data

open BigOperators MME MME.ProfiledCW MME.RecursiveYZ MME.CompleteSplit
open scoped Classical
set_option autoImplicit false

theorem mme_exact_step_source_add_parent_grading
    {ell N : ℕ} {P : Predicate N} (E : ExactStep ell N P) :
    ∃ F : ExactStep ell N (fun i x => P i x ∧
      ∀ (r : Fin E.hash.R) (t : Fin (E.hash.n r)),
        (∑ h : Fin 2, ∑ q,
          ((split E.stage.positions E.length x) ⟨r,t,h⟩ q).val) = E.hash.parent r i),
      F.count = E.count ∧ F.stage.repairExponent = E.stage.repairExponent ∧
      F.copies = E.copies ∧ F.output = E.output := by sorry
