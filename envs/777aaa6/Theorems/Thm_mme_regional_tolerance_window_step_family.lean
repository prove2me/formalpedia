-- Prove2me | Theorems.Thm_mme_regional_tolerance_window_step_family
-- name    : mme_regional_tolerance_window_step_family
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-21T21:20:29.446522+00:00
-- url     : https://prove2.me/theorems/8d5922ba-ef7d-4b2e-8ef7-c77527cea84f
-- title:
--   A polynomial exact-type extraction family for a physical tolerance window
-- statement:
--   Construct a finite family of actual integer extraction steps covering every CW-supported child word triple in a prescribed cell-frequency tolerance window, uniquely. Every step extracts from the same parent-mixture window of radius epsilon + 2 delta. The number of cases is bounded by (number of positions + 1)^(3 times number of cells times number of complete words). The only rate premise is the explicit scalar finite-loss budget for admissible nearby profiles; source inclusion, admissibility, and the type cover are proved.
-- source:
--   Finite physical tolerance-window extraction for the More Asymmetry proof.

import Definitions.Def_mme_regional_tolerance_window_data
import Theorems.Thm_mme_regional_parent_mixture_lipschitz
import Theorems.Thm_mme_regional_supported_histogram_admissibility
import Theorems.Thm_mme_prescribed_histogram_polynomial_type_cover
import Theorems.Thm_mme_regional_target_marginals
open BigOperators MME MME.ProfiledCW MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem mme_regional_tolerance_window_step_family {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (delta eps rate : ℝ) (hdelta : 0 ≤ delta) (heps : 0 < eps)
    (hsize : (8 * D.repairScale : ℝ) *
      (25 * D.R * (Fintype.card (CompleteWord ell) : ℝ)^2) ≤ (D.minimum : ℝ) * eps^2)
    (hbudget : ∀ mu : WindowProfile D, WindowAdmissible D mu →
      (∀ i, WindowClose D delta i (mu i)) → rate ≤ windowLogBudget D mu eps) :
    ∃ (types : ℕ) (steps : Fin types → IntegerStep ell M (parentWindow D (eps+2*delta))),
      types ≤ (Fintype.card (Position D.n) + 1) ^
        (3 * Fintype.card (Cell D.half D.R D.parent) * Fintype.card (CompleteWord ell)) ∧
      (∀ j, rate ≤ (steps j).certifiedLogCopies) ∧
      (∀ j i x, (steps j).output i x → childWindow D delta i x) ∧
      (∀ x : Fin 3 → FineWord M, supported x → (∀ i, childWindow D delta i (x i)) →
        ∃! j, ∀ i, (steps j).output i (x i)) := by
  sorry
