-- Prove2me | solution 1 for mme_global_frame_window_implies_regional_parent_typical
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T12:51:28.541795+00:00
-- url     : https://prove2.me/submissions/06f5109f-6c2c-4010-8b34-dce5c62bd8a2

import Definitions.Def_mme_complete_split_concatenation
import Definitions.Def_mme_global_CW_histogram_frame
import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_recursive_yz_cell_partition
import Mathlib.Algebra.Order.Field.Basic

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false

/-- Reading the two halves of each word preserves its exact histogram in a cell. -/
theorem mme_parent_pair_histogram_of_cell_fiber
    {P C A W : Type} [Fintype P] (cell : P → C) (f : P → A)
    (c : C) (n : ℕ) (fiber : Fin n ≃ {p : P // cell p = c})
    (pair : A ≃ (Fin 2 → W)) (w : Fin 2 → W) :
    Fintype.card {t : Fin n // ∀ h, pair (f (fiber t).val) h = w h} =
      count cell f c (pair.symm w) := by
  classical
  let e : {t : Fin n // ∀ h, pair (f (fiber t).val) h = w h} ≃
      {p : P // cell p = c ∧ f p = pair.symm w} := {
    toFun := fun t ↦ ⟨(fiber t.val).val, (fiber t.val).property,
      pair.injective ((funext t.property).trans (pair.apply_symm_apply w).symm)⟩
    invFun := fun p ↦ ⟨fiber.symm ⟨p.val,p.property.1⟩, by
      intro h
      simp only [Equiv.apply_symm_apply, p.property.2]⟩
    left_inv := by intro t; apply Subtype.ext; simp
    right_inv := by intro p; apply Subtype.ext; simp }
  calc
    _ = Fintype.card {p : P // cell p = c ∧ f p = pair.symm w} := Fintype.card_congr e
    _ = count cell f c (pair.symm w) := by rw [Fintype.card_subtype]; rfl

/-- A global histogram window gives a regional parent window after the exact
change of normalization from the total block count to each regional cell size. -/
theorem mme_parent_typical_of_global_histogram_window
    {P C A W : Type} [Fintype P] [Fintype W]
    {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ)
    (cell : P → C) (f : P → A) (region : Fin R → C)
    (fiber : ∀ r, Fin (n r) ≃ {p : P // cell p = region r})
    (pair : A ≃ (Fin 2 → W)) (center : C → A → ℝ)
    (total delta eps : ℝ) (htotal_pos : 0 < total) (hn : ∀ r, 0 < n r)
    (hwindow : ∀ r a, |(count cell f (region r) a : ℝ) / total -
      center (region r) a| ≤ delta)
    (hmixture : ∀ r w, parentMixture htotal n m mu r w =
      total / (n r : ℝ) * center (region r) (pair.symm w))
    (htolerance : ∀ r, total / (n r : ℝ) * delta < eps) :
    parentTypical htotal n m mu eps
      (fun p ↦ pair (f (fiber p.1 p.2.1).val) p.2.2) := by
  classical
  intro r w
  have hnreal : (0 : ℝ) < n r := by exact_mod_cast hn r
  have hcount := mme_parent_pair_histogram_of_cell_fiber cell f (region r)
    (n r) (fiber r) pair w
  change |(_ : ℝ) / (n r : ℝ) - parentMixture htotal n m mu r w| < eps
  have hcount' : Fintype.card {t : Fin (n r) // ∀ h,
      (fun p : Position n ↦ pair (f (fiber p.1 p.2.1).val) p.2.2) ⟨r,t,h⟩ = w h} =
      count cell f (region r) (pair.symm w) := hcount
  simp only [hcount', hmixture]
  have hid : (count cell f (region r) (pair.symm w) : ℝ) / (n r : ℝ) -
      total / (n r : ℝ) * center (region r) (pair.symm w) =
      (total / (n r : ℝ)) *
        ((count cell f (region r) (pair.symm w) : ℝ) / total -
          center (region r) (pair.symm w)) := by
    field_simp
  rw [hid, abs_mul, abs_of_pos (div_pos htotal_pos hnreal)]
  exact (mul_le_mul_of_nonneg_left (hwindow r (pair.symm w))
    (div_pos htotal_pos hnreal).le).trans_lt (htolerance r)

#print axioms mme_parent_pair_histogram_of_cell_fiber
#print axioms mme_parent_typical_of_global_histogram_window

open MME.CompleteSplit

private def wordPair (ell : ℕ) (hell : 1 ≤ ell) :
    CompleteWord (ell + 1) ≃ (Fin 2 → CompleteWord ell) :=
  (completeWordSplitEquiv ell hell).trans {
    toFun := fun w h ↦ if h = 0 then w.1 else w.2
    invFun := fun w ↦ (w 0, w 1)
    left_inv := by intro w; simp
    right_inv := by intro w; funext h; fin_cases h <;> simp }

/-- A global frame window induces regional parent windows on its literal two-half words.
The center-matching hypothesis isolates the numerical mixture identity. -/
theorem solution
    {ell M half R : ℕ} (hell : 1 ≤ ell)
    (D : GlobalCW.HistogramFrame (ell + 1) M)
    {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → CompleteWord ell → ℕ)
    (region : Fin R → Cell D.degree D.R D.bounds)
    (fiber : ∀ r, Fin (n r) ≃
      {p : GlobalCW.Place D.n // GlobalCW.cell D.reference p = region r})
    (center : Fin 3 → Cell D.degree D.R D.bounds → CompleteWord (ell + 1) → ℝ)
    (delta eps : ℝ) (hL : 0 < D.L) (hn : ∀ r, 0 < n r)
    (i : Fin 3) (x : ProfiledCW.FineWord M)
    (hwindow : D.window (fun i hist ↦ ∀ c w,
      |(hist c w : ℝ) / (D.L : ℝ) - center i c w| ≤ delta) i x)
    (hmixture : ∀ r (w : Fin 2 → CompleteWord ell),
      parentMixture htotal n m mu r w = (D.L : ℝ) / (n r : ℝ) *
        center i (region r) ((completeWordSplitEquiv ell hell).symm (w 0, w 1)))
    (htolerance : ∀ r, (D.L : ℝ) / (n r : ℝ) * delta < eps) :
    parentTypical htotal n m mu eps (fun p ↦
      let w := completeWordSplitEquiv ell hell
        (ProfiledCW.split D.positions D.length x (fiber p.1 p.2.1).val)
      if p.2.2 = 0 then w.1 else w.2) := by
  apply mme_parent_typical_of_global_histogram_window htotal m mu
    (GlobalCW.cell D.reference) (ProfiledCW.split D.positions D.length x) region fiber
    (wordPair ell hell) (center i) (D.L : ℝ) delta eps
  · exact_mod_cast hL
  · exact hn
  · intro r a
    exact hwindow.2 (region r) a
  · exact hmixture
  · exact htolerance

#print axioms solution
