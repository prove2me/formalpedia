-- Prove2me | solution 1 for SIC_POVM_Conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T07:07:15.047925+00:00
-- url     : https://prove2.me/submissions/7e3c172f-1617-4191-a71e-a54f05cbcc77
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeylHeisenbergSIC_exists_of_fiducial
import Theorems.Thm_WeylHeisenbergSIC_fiducial_exists
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators

/-- The general SIC conjecture follows from the stronger fiducial existence conjecture. -/
theorem solution :
    ∀ d : ℕ, 1 ≤ d →
      ∃ Φ : Fin (d ^ 2) → EuclideanSpace ℂ (Fin d),
        (∀ i, ‖Φ i‖ = 1) ∧
        Pairwise (fun i j =>
          Complex.normSq (∑ k : Fin d, star (Φ i k) * Φ j k) = (d + 1 : ℝ)⁻¹) := by
  intro d hd
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨ψ, hnorm, hfid⟩ := WeylHeisenbergSIC.fiducial_exists d
  exact WeylHeisenbergSIC.exists_of_fiducial d ψ hnorm hfid
