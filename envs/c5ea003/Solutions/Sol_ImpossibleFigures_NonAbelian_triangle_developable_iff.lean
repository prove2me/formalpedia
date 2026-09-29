-- Prove2me | solution 1 for ImpossibleFigures.NonAbelian.triangle_developable_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T07:05:53.436478+00:00
-- url     : https://prove2.me/submissions/3fc1c2f5-0cd5-4b89-b2ab-8ae2ff798551

import Mathlib
import Definitions.Def_Geometry_NonAbelianHolonomy

open ImpossibleFigures.NonAbelian

variable {G : Type*} [Group G]

theorem solution (ω : Fin 3 → G) :
    Developable triS triT ω ↔ ω 2 * ω 1 * ω 0 = 1 := by
  constructor
  · rintro ⟨H, hH⟩
    have h0 : ω 0 = H 1 * (H 0)⁻¹ := by simpa [triS, triT] using hH 0
    have h1 : ω 1 = H 2 * (H 1)⁻¹ := by simpa [triS, triT] using hH 1
    have h2 : ω 2 = H 0 * (H 2)⁻¹ := by
      simpa [triS, triT, show (2 : Fin 3) + 1 = 0 from rfl] using hH 2
    calc ω 2 * ω 1 * ω 0
        = (H 0 * (H 2)⁻¹) * (H 2 * (H 1)⁻¹) * (H 1 * (H 0)⁻¹) := by
            rw [h0, h1, h2]
      _ = H 0 * ((H 2)⁻¹ * H 2) * ((H 1)⁻¹ * H 1) * (H 0)⁻¹ := by
            simp [mul_assoc]
      _ = H 0 * 1 * 1 * (H 0)⁻¹ := by simp
      _ = 1 := by simp
  · intro h
    refine ⟨![1, ω 0, ω 1 * ω 0], ?_⟩
    intro e
    have hω2 : ω 2 = (ω 1 * ω 0)⁻¹ :=
      mul_eq_one_iff_eq_inv.mp (by simpa [mul_assoc] using h)
    fin_cases e
    · -- e = 0
      change ω 0 = (![1, ω 0, ω 1 * ω 0] : Fin 3 → G) 1 *
        ((![1, ω 0, ω 1 * ω 0] : Fin 3 → G) 0)⁻¹
      simp
    · change ω 1 = (![1, ω 0, ω 1 * ω 0] : Fin 3 → G) 2 *
        ((![1, ω 0, ω 1 * ω 0] : Fin 3 → G) 1)⁻¹
      simp [mul_assoc]
    · change ω 2 = (![1, ω 0, ω 1 * ω 0] : Fin 3 → G) 0 *
        ((![1, ω 0, ω 1 * ω 0] : Fin 3 → G) 2)⁻¹
      simpa using hω2
