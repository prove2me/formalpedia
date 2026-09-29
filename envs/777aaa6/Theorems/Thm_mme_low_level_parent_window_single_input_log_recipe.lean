-- Prove2me | Theorems.Thm_mme_low_level_parent_window_single_input_log_recipe
-- name    : mme_low_level_parent_window_single_input_log_recipe
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T12:10:56.302521+00:00
-- url     : https://prove2.me/theorems/4623db12-9558-436a-9820-c0990c34485e
-- title:
--   One-input terminal extraction from an elementary parent window
-- statement:
--   Let $D$ be an integer regional extraction step at depth $\ell\le1$, and choose a higher recipe level $u>\ell$. Let $0<\varepsilon\le\eta$ satisfy the step's scalar size test at tolerance $\varepsilon$. If $r\ge0$ is bounded by the explicit logarithmic copy budget of the central profile at tolerance $\varepsilon$, then the parent window of radius $\eta$ admits a logarithmic recipe with
--   \[
--   \mathrm{inputs}=1,\qquad \log\mathrm{outputs}=r.
--   \]
--   For every partition into physical reference cells, the recipe retains oriented boundary profiles reproducing all prescribed cell grades and histograms. Its three matrix dimensions are the products of the corresponding oriented profile dimensions. The budget hypothesis concerns only the central profile; no terminal interface or budget over all profiles in the window is assumed.
-- source:
--   Exact integer regional profiles, tolerance windows and terminal CW recipes.

import Definitions.Def_mme_logarithmic_regional_CW_recipe
import Definitions.Def_mme_regional_tolerance_window_data

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary MME.ProfiledCW
set_option autoImplicit false


open MME.RegionRealization

theorem mme_low_level_parent_window_single_input_log_recipe
    {ell M upper : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (hlevel : ell ≤ 1) (hupper : ell < upper)
    (part : Partition (fullCell D.total D.reference))
    (eps eta rate : ℝ) (heps : 0 < eps) (heta : eps ≤ eta)
    (hrate : 0 ≤ rate)
    (hsize : (8 * D.repairScale : ℝ) *
      (25 * D.R * (Fintype.card (CompleteWord ell) : ℝ)^2) ≤
        (D.minimum : ℝ) * eps^2)
    (hbudget : rate ≤ windowLogBudget D D.mu eps) :
    ∃ (z : Fin part.parts → Fin 3)
      (profiles : ∀ j, Boundary.Profile ell (part.size j)),
      (∀ j i, ((part.cells j).2.val i).val = (profiles j).shape (z j) i) ∧
      (∀ j i, D.mu i (part.cells j) = (profiles j).mu (z j) i) ∧
      ∃ E : LogRecipe M upper (parentWindow D eta),
        E.inputs = 1 ∧ E.logOutputs = rate ∧
        E.dims = (∏ j, (profiles j).a (z j),
          ∏ j, (profiles j).b (z j), ∏ j, (profiles j).c (z j)) := by sorry
