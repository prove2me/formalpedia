-- Prove2me | solution 1 for BookSixth.isUnlink_path_image
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T07:54:06.997361+00:00
-- url     : https://prove2.me/submissions/8f6a4c15-298e-4323-8c41-66267a2896f3

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution {m : ℕ}
    (C : Fin m → Set Space3)
    (K : ℝ → Space3 ≃ₜ Space3)
    (hK : Continuous (fun p : ℝ × Space3 => K p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K 0 x = x))
    (hC : IsUnlink C) :
    IsUnlink (fun i => K 1 '' C i) := by
  obtain ⟨H, hH1, hH2, hH0, hH1'⟩ := hC
  let J : ℝ → Space3 ≃ₜ Space3 := fun t => (K t).symm.trans (H t)
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · simpa [J, Homeomorph.trans_apply] using
      hH1.comp₂ continuous_fst hK.2.1
  · simpa [J, Homeomorph.symm_trans_apply] using
      hK.1.comp₂ continuous_fst hH2
  · intro x
    have hK0symm : (K 0).symm x = x := by
      have h := congrArg (K 0).symm (hK.2.2 x)
      simpa using h.symm
    simp [J, Homeomorph.trans_apply, hH0, hK0symm]
  · intro i
    calc
      (J 1) '' (K 1 '' C i) = H 1 '' ((K 1).symm '' (K 1 '' C i)) := by
        have hJ1 : J 1 = H 1 ∘ (K 1).symm := by
          funext x
          rfl
        rw [hJ1, Set.image_comp]
      _ = H 1 '' C i := by
        have hKinv : (K 1).symm '' ((K 1) '' C i) = C i := by
          rw [Set.image_image]
          simp
        rw [hKinv]
      _ = standardCircle i.val := hH1' i
