-- Prove2me | solution 1 for mme_released_global_joint_window_family
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T16:15:22.703858+00:00
-- url     : https://prove2.me/submissions/9eb8c404-8b15-4de0-b0a6-0b4ce85cdf11

import Definitions.Def_mme_released_global_joint_interface
import Theorems.Thm_mme_released_global_physical_orientation
import Theorems.Thm_mme_released_global_numerical_window_extraction
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.ReleasedGlobal
set_option autoImplicit false
set_option maxHeartbeats 1000000
attribute [local irreducible] frame windowGood physicalPart

theorem solution (eta : Fin 6 → ℝ) (heta : ∀ o, 0 < eta o) :
    ∃ eps : Fin 6 → ℝ, (∀ o, 0 < eps o) ∧ (∀ o, eps o ≤ eta o) ∧
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ hk : 0 < k^2,
      ∃ a : ∀ o : Fin 6, Reference o (k^2),
      ∃ S : ∀ o, Part (4 * blocks (k^2)) 3 (physicalWindow o (k^2) hk (a o) (eps o)),
        ∀ o, 1 ≤ (S o).inputs ∧ (S o).inputs ≤ (blocks (k^2)+1)^10935 ∧
          usableRate o * (blocks (k^2) : ℝ) + Real.log ((S o).inputs : ℝ) ≤
            (S o).rate := by
  classical
  have hr (o : Fin 6) : 0 ≤ usableRate o ∧
      usableRate o < (ReleasedGlobalNumeric.rateFloor o : ℝ) := by
    fin_cases o <;> norm_num [usableRate,ReleasedGlobalNumeric.rateFloor]
  have h (o : Fin 6) := mme_released_global_numerical_window_extraction
    (K := ℚ) o (usableRate o) (eta o) (hr o).1 (hr o).2 (heta o)
  choose eps heps hcap k0 hsteps using h
  refine ⟨eps,heps,hcap,Finset.univ.sup k0,?_⟩
  intro k hk0
  have hs (o : Fin 6) := hsteps o k
    ((Finset.le_sup (f := k0) (Finset.mem_univ o)).trans hk0)
  choose hk a S hlo hhi hrate hrestriction using hs
  refine ⟨hk 0,a,fun o ↦ physicalPart o (S o),?_⟩
  intro o
  change 1 ≤ (physicalPart o (S o)).inputs ∧
    (physicalPart o (S o)).inputs ≤ (blocks (k^2)+1)^10935 ∧
    usableRate o * (blocks (k^2) : ℝ) +
      Real.log ((physicalPart o (S o)).inputs : ℝ) ≤ (physicalPart o (S o)).rate
  obtain ⟨hi,hr⟩ := mme_released_global_physical_orientation.2 o (S o)
  rw [hi,hr]
  exact ⟨hlo o,hhi o,hrate o⟩
