-- Prove2me | solution 1 for BookSixth.round_circle_snoc_transport_compose_v4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T07:21:30.509711+00:00
-- url     : https://prove2.me/submissions/ae88b8ab-8f53-4c98-9ff7-047931cf93f6

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution {n : ℕ}
    (C : Fin n → Set Space3)
    (D : Set Space3)
    (L : ℝ → Space3 ≃ₜ Space3)
    (G : ℝ → Space3 ≃ₜ Space3)
    (hL : Continuous (fun p : ℝ × Space3 => L p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (L p.1).symm p.2) ∧
      (∀ x, L 0 x = x))
    (hG : Continuous (fun p : ℝ × Space3 => G p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (G p.1).symm p.2) ∧
      (∀ x, G 0 x = x))
    (hLold : ∀ i, (L 1) '' C i = standardCircle i.val)
    (hGnew : (G 1) '' (L 1) '' D = standardCircle n)
    (hGprefix : ∀ i : Fin n,
      (G 1) '' standardCircle i.val = standardCircle i.val) :
    ∃ H : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => H p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (∀ i, (H 1) '' C i = standardCircle i.val) ∧
      (H 1) '' D = standardCircle n := by
  let H : ℝ → Space3 ≃ₜ Space3 := fun t => (L t).trans (G t)
  refine ⟨H, ?_, ?_, ?_, ?_, ?_⟩
  · have hmap : Continuous (fun p : ℝ × Space3 =>
        (p.1, (L p.1) p.2)) :=
      continuous_fst.prodMk hL.1
    simpa [H, Function.comp_def] using hG.1.comp hmap
  · have hmap : Continuous (fun p : ℝ × Space3 =>
        (p.1, (G p.1).symm p.2)) :=
      continuous_fst.prodMk hG.2.1
    simpa [H, Function.comp_def] using hL.2.1.comp hmap
  · intro x
    simp [H, hL.2.2 x, hG.2.2 x]
  · intro i
    calc
      (H 1) '' C i = (fun x => G 1 (L 1 x)) '' C i := by rfl
      _ = G 1 '' (L 1 '' C i) := by rw [Set.image_image]
      _ = G 1 '' standardCircle i.val := by rw [hLold i]
      _ = standardCircle i.val := hGprefix i
  · calc
      (H 1) '' D = (fun x => G 1 (L 1 x)) '' D := by rfl
      _ = G 1 '' (L 1 '' D) := by rw [Set.image_image]
      _ = standardCircle n := hGnew
