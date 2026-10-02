-- Prove2me | solution 1 for BookSixth.round_circle_snoc_transport_compose_supported
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T22:47:25.716682+00:00
-- url     : https://prove2.me/submissions/729b0b71-3746-4ed0-87a2-c7413aea0161

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution {n : ℕ}
    (C : Fin n → Set Space3) (D : Set Space3)
    (K : ℝ → Space3 ≃ₜ Space3)
    (G : ℝ → Space3 ≃ₜ Space3)
    (hK : Continuous (fun p : ℝ × Space3 => K p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K 0 x = x))
    (hG : Continuous (fun p : ℝ × Space3 => G p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (G p.1).symm p.2) ∧
      (∀ x, G 0 x = x))
    (hKold : ∀ i, (K 1) '' C i = standardCircle i.val)
    (hKnew : ∀ t, K t '' D = D)
    (hGnew : (G 1) '' D = standardCircle n)
    (hGstandard : ∀ i : Fin n,
      (G 1) '' standardCircle i.val = standardCircle i.val) :
    ∃ H : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => H p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (∀ i, (H 1) '' C i = standardCircle i.val) ∧
      (H 1) '' D = standardCircle n := by
  let H : ℝ → Space3 ≃ₜ Space3 := fun t => (K t).trans (G t)
  refine ⟨H, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [H, Homeomorph.trans_apply] using
      hG.1.comp₂ continuous_fst hK.1
  · simpa [H, Homeomorph.symm_trans_apply] using
      hK.2.1.comp₂ continuous_fst hG.2.1
  · intro x
    simp [H, hK.2.2 x, hG.2.2 x]
  · intro i
    have hC :
        (G 1 ∘ K 1) '' C i = standardCircle i.val := by
      rw [Set.image_comp, hKold i, hGstandard i]
    simpa [H, Homeomorph.trans_apply] using hC
  · have hD :
        (G 1 ∘ K 1) '' D = standardCircle n := by
      rw [Set.image_comp, hKnew 1, hGnew]
    simpa [H, Homeomorph.trans_apply] using hD
