-- Prove2me | Theorems.Thm_mme_child_grading_implies_parent_grading
-- name    : mme_child_grading_implies_parent_grading
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:43:48.890617+00:00
-- url     : https://prove2.me/theorems/6f1aba6a-b2ef-4895-b5a0-a843baec7622
-- title:
--   Complementary child grades recover parent grades
-- statement:
--   For any regional address, a word satisfying its child grading has the prescribed parent grade at each parent position: the two child grades sum to that parent grade.
-- source:
--   Exact regional extraction and complementary child grades.

import Definitions.Def_mme_recursive_profiled_CW_data

open BigOperators MME MME.ProfiledCW MME.RecursiveYZ MME.CompleteSplit
open scoped Classical
set_option autoImplicit false

theorem mme_child_grading_implies_parent_grading
    {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (i : Fin 3) (a : Address half R parent n) (f : Position n → CompleteWord ell)
    (hf : Graded htotal i a f) (r : Fin R) (t : Fin (n r)) :
    (∑ h : Fin 2, ∑ q, (f ⟨r,t,h⟩ q).val) = parent r i := by sorry
