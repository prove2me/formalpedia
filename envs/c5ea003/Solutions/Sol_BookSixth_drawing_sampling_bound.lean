-- Prove2me | solution 1 for BookSixth.drawing_sampling_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T13:03:28.845823+00:00
-- url     : https://prove2.me/submissions/a944ff6c-8aa8-466c-8c4a-c5e2021d22bb

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_sampling_averaging_bound
import Theorems.Thm_BookSixth_crossing_free_subset_edge_bound
open scoped BigOperators
open BookSixth

theorem solution {N M : ℕ} (D : PlaneDrawing N M) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p^2 * (M : ℝ) ≤ 3*p*(N : ℝ) + p^4*(D.crossings.card : ℝ) := by
  classical
  apply BookSixth.sampling_averaging_bound D ?_ p hp hp1
  intro x
  let V : Finset (Fin N) := Finset.univ.filter (fun v => x v = true)
  let A : Finset (Fin M) := Finset.univ.filter
    (fun e => x (D.left e) = true ∧ x (D.right e) = true)
  let C := D.crossings.filter (fun c =>
    x (D.left c.1.1) = true ∧ x (D.right c.1.1) = true ∧
    x (D.left c.1.2) = true ∧ x (D.right c.1.2) = true)
  let R : Finset (Fin M) := C.image (fun c => c.1.1)
  let E : Finset (Fin M) := A \ R
  have hR : R.card ≤ C.card := Finset.card_image_le
  have hcount : A.card ≤ E.card + C.card := by
    have h := Finset.card_le_card_sdiff_add_card (s := A) (t := R)
    change A.card ≤ E.card + R.card at h
    omega
  have hsel {e : Fin M} (he : e ∈ E) :
      x (D.left e) = true ∧ x (D.right e) = true := by
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp he).1).2
  have hend : ∀ e ∈ E, D.left e ∈ V ∧ D.right e ∈ V := by
    intro e he
    simpa [V] using hsel he
  have hfree : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → ∀ t s : EdgeParameter,
      0 < t.val → t.val < 1 → 0 < s.val → s.val < 1 →
      D.arc e t ≠ D.arc f s := by
    intro e he f hf hef t s ht0 ht1 hs0 hs1 heq
    have hen : e ∉ R := (Finset.mem_sdiff.mp he).2
    have hfn : f ∉ R := (Finset.mem_sdiff.mp hf).2
    have hse := hsel he
    have hsf := hsel hf
    rcases lt_or_gt_of_ne hef with hlt | hgt
    · have hc : ((e, f), D.arc e t) ∈ D.crossings :=
        (D.crossings_exact e f (D.arc e t)).mpr
          ⟨hlt, t, s, ht0, ht1, hs0, hs1, rfl, heq.symm⟩
      have hcC : ((e, f), D.arc e t) ∈ C :=
        Finset.mem_filter.mpr ⟨hc, hse.1, hse.2, hsf.1, hsf.2⟩
      exact hen (Finset.mem_image_of_mem (fun c => c.1.1) hcC)
    · have hc : ((f, e), D.arc f s) ∈ D.crossings :=
        (D.crossings_exact f e (D.arc f s)).mpr
          ⟨hgt, s, t, hs0, hs1, ht0, ht1, rfl, heq⟩
      have hcC : ((f, e), D.arc f s) ∈ C :=
        Finset.mem_filter.mpr ⟨hc, hsf.1, hsf.2, hse.1, hse.2⟩
      exact hfn (Finset.mem_image_of_mem (fun c => c.1.1) hcC)
  have hplanar : E.card ≤ 3 * V.card :=
    BookSixth.crossing_free_subset_edge_bound D V E hend hfree
  have hnat : A.card ≤ 3 * V.card + C.card := by omega
  have hreal : (A.card : ℝ) ≤ 3 * (V.card : ℝ) + (C.card : ℝ) := by
    exact_mod_cast hnat
  simpa only [A, V, C, Finset.natCast_card_filter] using hreal
