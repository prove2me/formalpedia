-- Prove2me | solution 1 for KeplerMission.nonlinear_catalog_valid
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-28T00:57:24.790276+00:00
-- url     : https://prove2.me/submissions/bbf33a77-65c5-4470-b8e1-4fa044787b6b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_KeplerMission_nonlinear_packing_catalog_valid
import Theorems.Thm_KeplerMission_nonlinear_ox3q1h_catalog_valid
import Theorems.Thm_KeplerMission_nonlinear_terminal_catalog_valid
import Theorems.Thm_KeplerMission_nonlinear_linear_relaxation_catalog_valid
import Theorems.Thm_KeplerMission_nonlinear_8055810915_valid

set_option autoImplicit false
set_option maxRecDepth 2048

namespace KeplerMission.Nonlinear

-- The exact 28 tameness records occur in the 127-entry LP selector.
-- The equality checks the concrete record at every index, not just source labels.
private theorem tameness_subset_linearRelaxation :
    tamenessCatalog ⊆ linearRelaxationCatalog := by
  let indices : List (Fin 127) :=
    [0, 1, 2, 3, 4, 11, 12, 13, 14, 15, 16, 17, 18, 21, 22, 23, 24, 25,
      26, 27, 28, 36, 37, 38, 39, 40, 50, 126]
  have h : tamenessCatalog = indices.map
      (fun i ↦ linearRelaxationCatalog[i.val]'(by change i.val < 127; exact i.isLt)) := rfl
  rw [h]
  intro p hp
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
  exact List.mem_of_getElem (l := linearRelaxationCatalog) (i := i.val)
    (h := by change i.val < 127; exact i.isLt) rfl

-- Of the five YSSKQOY packing-separation records, only WAZLDCD 8055810915
-- is absent from packingCatalog. The other four memberships are kernel-checked.
private theorem packingSeparation_valid_of_packing
    (hp : ∀ p ∈ packingCatalog, p.Valid) (h309 : problem309.Valid) :
    ∀ p ∈ packingSeparationCatalog, p.Valid := by
  intro p h
  simp only [packingSeparationCatalog, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact hp _ (List.mem_of_getElem (i := 77) (h := by decide) rfl)
  · exact hp _ (List.mem_of_getElem (i := 78) (h := by decide) rfl)
  · exact h309
  · exact hp _ (List.mem_of_getElem (i := 79) (h := by decide) rfl)
  · exact hp _ (List.mem_of_getElem (i := 80) (h := by decide) rfl)

/-- Exact assembly of all six fixed source selectors from four principal families
and the remaining WAZLDCD record. Source: Hales et al. (2017), Section 5, PDF p. 12,
equation (2), and Section 6, PDF pp. 16–17; Flyspeck `the_main_statement.hl:55–59`.
This is a conditional theorem; the five nonlinear inputs are not proved here. -/
theorem catalogValid_of_four_families_and_wazldcd
    (hp : ∀ p ∈ packingCatalog, p.Valid)
    (ho : ∀ p ∈ ox3q1hCatalog, p.Valid)
    (ht : ∀ p ∈ terminalCatalog, p.Valid)
    (hl : ∀ p ∈ linearRelaxationCatalog, p.Valid)
    (h309 : problem309.Valid) : CatalogValid := by
  intro p h
  simp only [catalog, List.mem_append] at h
  rcases h with (((((h | h) | h) | h) | h) | h)
  · exact hp p h
  · exact ho p h
  · exact ht p h
  · exact hl p h
  · exact packingSeparation_valid_of_packing hp h309 p h
  · exact hl p (tameness_subset_linearRelaxation h)

end KeplerMission.Nonlinear

open KeplerMission

theorem solution : Nonlinear.CatalogValid :=
  Nonlinear.catalogValid_of_four_families_and_wazldcd
    nonlinear_packing_catalog_valid nonlinear_ox3q1h_catalog_valid
    nonlinear_terminal_catalog_valid nonlinear_linear_relaxation_catalog_valid
    nonlinear_8055810915_valid
