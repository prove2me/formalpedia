-- Prove2me | solution 1 for LinearOptimization.ellipsoid_update_halfspace_volume
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-09T17:06:28.631378+00:00
-- url     : https://prove2.me/submissions/b2f09a89-0621-4321-9914-6d6ed7cc7317

import Theorems.Thm_LinearOptimization_ellipsoid_update_matrix_posDef
import Theorems.Thm_LinearOptimization_ellipsoid_update_halfspace_subset
import Theorems.Thm_LinearOptimization_ellipsoid_update_volume_lt

open Matrix MeasureTheory

theorem solution {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    (LinearOptimization.ellipsoidUpdateMatrix D a).PosDef ∧
    LinearOptimization.ellipsoid z D ∩ {x | a ⬝ᵥ z ≤ a ⬝ᵥ x} ⊆
      LinearOptimization.ellipsoid
        (LinearOptimization.ellipsoidUpdateCenter z D a)
        (LinearOptimization.ellipsoidUpdateMatrix D a) ∧
    volume (LinearOptimization.ellipsoid
        (LinearOptimization.ellipsoidUpdateCenter z D a)
        (LinearOptimization.ellipsoidUpdateMatrix D a)) <
      ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * ((n : ℝ) + 1)))) *
        volume (LinearOptimization.ellipsoid z D) := by
  exact ⟨
    LinearOptimization.ellipsoid_update_matrix_posDef hn D hD a ha,
    LinearOptimization.ellipsoid_update_halfspace_subset hn z D hD a ha,
    LinearOptimization.ellipsoid_update_volume_lt hn z D hD a ha⟩
