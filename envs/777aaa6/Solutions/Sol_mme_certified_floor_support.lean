-- Prove2me | solution 1 for mme_certified_floor_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T05:22:35.038984+00:00
-- url     : https://prove2.me/submissions/10565cd5-d04a-42d0-949e-74cddbd006be

import Mathlib
import Definitions.Def_mme_certified_generic_floor_data
import Definitions.Def_mme_certified_entropy_rational_data

open BigOperators MME MME.RegionRate MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u


namespace MME.Cert

/-- A certified floor only sees the support of its distribution, so off-support letters cost
nothing. -/
theorem regFloorG_support {W : Type u} [Fintype W] (p : W → ℚ) (e : W → Fin 4 → ℤ)
    (S : Finset W) (hS : ∀ w, w ∉ S → p w = 0) :
    regFloorG p e =
      (∑ w ∈ S, (p w - (p w) ^ 2 / qvalQ (e w))) -
        ∑ j, (if 0 ≤ (∑ w ∈ S, p w * ((e w j : ℤ) : ℚ)) then
                (∑ w ∈ S, p w * ((e w j : ℤ) : ℚ)) * logHi j
              else (∑ w ∈ S, p w * ((e w j : ℤ) : ℚ)) * logLo j) := by
  classical
  have hquad : ∑ w ∈ S, (p w - (p w) ^ 2 / qvalQ (e w)) =
      ∑ w, (p w - (p w) ^ 2 / qvalQ (e w)) := by
    refine Finset.sum_subset (Finset.subset_univ S) (fun w _ hw ↦ ?_)
    rw [hS w hw]
    norm_num
  have hlin : ∀ j : Fin 4, ∑ w ∈ S, p w * ((e w j : ℤ) : ℚ) =
      ∑ w, p w * ((e w j : ℤ) : ℚ) := by
    intro j
    refine Finset.sum_subset (Finset.subset_univ S) (fun w _ hw ↦ ?_)
    rw [hS w hw]
    ring
  unfold regFloorG
  rw [hquad]
  congr 1
  exact Finset.sum_congr rfl (fun j _ ↦ by rw [hlin j])


end MME.Cert

theorem solution :
    ∀ {W : Type u} [Fintype W] (p : W → ℚ) (e : W → Fin 4 → ℤ) (S : Finset W),
      (∀ w, w ∉ S → p w = 0) →
      regFloorG p e =
        (∑ w ∈ S, (p w - (p w) ^ 2 / qvalQ (e w))) -
          ∑ j, (if 0 ≤ (∑ w ∈ S, p w * ((e w j : ℤ) : ℚ)) then
                  (∑ w ∈ S, p w * ((e w j : ℤ) : ℚ)) * logHi j
                else (∑ w ∈ S, p w * ((e w j : ℤ) : ℚ)) * logLo j) :=
  fun {W} _ p e S hS ↦ MME.Cert.regFloorG_support p e S hS
