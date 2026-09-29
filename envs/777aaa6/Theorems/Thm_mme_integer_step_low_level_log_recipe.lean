-- Prove2me | Theorems.Thm_mme_integer_step_low_level_log_recipe
-- name    : mme_integer_step_low_level_log_recipe
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T12:03:28.761898+00:00
-- url     : https://prove2.me/theorems/20aca569-0844-4792-ad72-9d0f7deed06a
-- title:
--   A complete logarithmic recipe for an elementary-depth regional extraction
-- statement:
--   Let D be an integer regional extraction step at level ell <= 1, and let upper > ell. Choose a nonnegative rate r bounded by D's certified logarithmic copy budget. Then there is a logarithmic recipe at level upper for the source predicate of D, with exactly one input and logarithmic output budget r. For any partition of the physical positions by full reference cells, the recipe retains oriented boundary profiles reproducing all cell grades and mode histograms. Its three matrix dimensions are the corresponding profile dimension products. Thus the terminal stage requires no separately supplied boundary interface or tensor alignment.
-- source:
--   Integer regional CW extraction, exact boundary profiles, and logarithmic recipe budgets.

import Definitions.Def_mme_logarithmic_regional_CW_recipe

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary MME.ProfiledCW
set_option autoImplicit false


open MME.RegionRealization

theorem mme_integer_step_low_level_log_recipe
    {ell M upper : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (hlevel : ell ≤ 1) (hupper : ell < upper)
    (part : Partition (fullCell D.total D.reference))
    (rate : ℝ) (hrate : 0 ≤ rate) (hbudget : rate ≤ D.certifiedLogCopies) :
    ∃ (z : Fin part.parts → Fin 3)
      (profiles : ∀ j, Boundary.Profile ell (part.size j)),
      (∀ j i, ((part.cells j).2.val i).val = (profiles j).shape (z j) i) ∧
      (∀ j i, D.mu i (part.cells j) = (profiles j).mu (z j) i) ∧
      ∃ E : LogRecipe M upper P,
        E.inputs = 1 ∧ E.logOutputs = rate ∧
        E.dims = (∏ j, (profiles j).a (z j),
          ∏ j, (profiles j).b (z j), ∏ j, (profiles j).c (z j)) := by sorry
