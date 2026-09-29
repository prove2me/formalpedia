-- Prove2me | Theorems.Thm_mme_integer_step_low_level_integer_recipe
-- name    : mme_integer_step_low_level_integer_recipe
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T12:01:52.686843+00:00
-- url     : https://prove2.me/theorems/9a2d9cdb-8920-4e11-852d-d94661136568
-- title:
--   A complete integer recipe for one elementary-depth regional extraction
-- statement:
--   Let D be an integer regional extraction step at level ell <= 1, and let upper > ell. Then there is an integer recipe at level upper for D's source predicate with exactly one input and D.copies outputs. For any physical full-cell partition, the recipe retains boundary profiles agreeing with all cell grades and mode histograms, and its dimensions are their three oriented dimension products. The recipe consists of the regional extraction followed by its constructed terminal boundary interface. The statement retains the guaranteed copy count without asserting that it is positive.
-- source:
--   Integer regional CW extraction and exact complementary boundary profiles.

import Definitions.Def_mme_integer_regional_CW_recipe

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary MME.ProfiledCW
set_option autoImplicit false


open MME.RegionRealization

theorem mme_integer_step_low_level_integer_recipe
    {ell M upper : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (hlevel : ell ≤ 1) (hupper : ell < upper)
    (part : Partition (fullCell D.total D.reference)) :
    ∃ (z : Fin part.parts → Fin 3)
      (profiles : ∀ j, Boundary.Profile ell (part.size j)),
      (∀ j i, ((part.cells j).2.val i).val = (profiles j).shape (z j) i) ∧
      (∀ j i, D.mu i (part.cells j) = (profiles j).mu (z j) i) ∧
      ∃ E : IntegerRecipe M upper P,
        E.inputs = 1 ∧ E.outputs = D.copies ∧
        E.dims = (∏ j, (profiles j).a (z j),
          ∏ j, (profiles j).b (z j), ∏ j, (profiles j).c (z j)) := by sorry
