-- Prove2me | solution 1 for mme_released_global_normalized_cells_matrix_product_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T02:42:28.599987+00:00
-- url     : https://prove2.me/submissions/2569edbc-5476-4b1c-962b-11e61d2caefa

import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Theorems.Thm_mme_finite_MM_extractions_kronFin_tau_product
import Theorems.Thm_mme_toQ_kronFin
import Theorems.Thm_mme_sixSymmetrization_restrict
import Definitions.Def_mme_released_global_frame_data
import Definitions.Def_mme_global_CW_histogram_frame
import Theorems.Thm_mme_basis_projected_family_restrict
import Definitions.Def_mme_recursive_yz_cell_partition
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Theorems.Thm_mme_kronPow_fiber_grouping_preserves_tensor_and_basis
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes

open BigOperators MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells
  MME.CompleteSplit Module PiTensorProduct
open scoped Classical
set_option autoImplicit false
universe u v w

/-- Arbitrary cellwise word windows can be extracted simultaneously when their
conjunction implies the global window. No exact-histogram assumption is needed. -/
private theorem mme_cell_window_product_restriction
    {K : Type u} [Field K] {P : Type v} {C : Type w} [Fintype P]
    (q ell L : ℕ) (positions : Fin L ≃ P) (cell : P → C)
    (D : Partition cell)
    (localWindow : ∀ j : Fin D.parts, Fin 3 → WordIndex.{u} q ell (D.size j) → Prop)
    (globalWindow : Fin 3 → WordIndex.{u} q ell L → Prop)
    (hwindow : ∀ i x, (∀ j, localWindow j i
      (fun a => x (D.leaves ell L positions ⟨j,a⟩))) → globalWindow i x) :
    Restrict
      (kronFin D.parts (fun j =>
        (source K q ell (D.size j)).basisAllAllowedSubtensor
          (basis K q ell (D.size j)) (localWindow j)))
      ((source K q ell L).basisAllAllowedSubtensor
        (basis K q ell L) globalWindow) := by
  classical
  let raw := fun j : Fin D.parts => source K q ell (D.size j)
  let child := fun j : Fin D.parts => (raw j).basisAllAllowedSubtensor
    (basis K q ell (D.size j)) (localWindow j)
  let G := fun j : Fin D.parts => (raw j).basisAllAllowedGrading
    (basis K q ell (D.size j)) (localWindow j)
  let proj := fun j i => (G j).blockProj i 0
  obtain ⟨Φ, ht, hb⟩ := mme_kronPow_fiber_grouping_preserves_tensor_and_basis
    (CWObj K q) (fun i => (MME.DWZStep1Support.cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm)
    (fun j => D.size j * 2 ^ (ell - 1)) (D.leaves ell L positions).symm
  change PiTensorProduct.map (fun i => (Φ i).toLinearMap) (source K q ell L).t =
    (kronFin D.parts raw).t at ht
  have hB (i : Fin 3) (x : WordIndex.{u} q ell L) :
      Φ i (basis K q ell L i x) =
        kronFinModePiBasis D.parts raw i (fun j => basis K q ell (D.size j) i)
          (fun j a => x (D.leaves ell L positions ⟨j,a⟩)) := hb i x
  let F := fun i => (kronFinFamilyModeMap D.parts raw child proj i).comp (Φ i).toLinearMap
  apply mme_restrict_basisAllAllowedSubtensor_of_vanishes (source K q ell L)
    (kronFin D.parts child) (basis K q ell L) globalWindow F
  · change PiTensorProduct.map (fun i =>
      (kronFinFamilyModeMap D.parts raw child proj i).comp (Φ i).toLinearMap)
        (source K q ell L).t = _
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
    exact (congrArg (PiTensorProduct.map
      (kronFinFamilyModeMap D.parts raw child proj)) ht).trans
      (kronFinFamilyModeMap_preserves_tensor raw child proj (fun _ => rfl))
  · intro i x hx
    change kronFinFamilyModeMap D.parts raw child proj i
      (Φ i (basis K q ell L i x)) = 0
    rw [hB]
    apply kronFinFamilyModeMap_basis_eq_zero_of_exists raw child i
      (fun j => basis K q ell (D.size j) i) proj
    have hn : ¬ ∀ j, localWindow j i
        (fun a => x (D.leaves ell L positions ⟨j,a⟩)) :=
      fun h => hx (hwindow i x h)
    obtain ⟨j, hj⟩ := not_forall.mp hn
    refine ⟨j, ?_⟩
    apply TensorObj.TypeGrading.blockProj_apply_mem_ne (G j) i 0 1 (by decide)
    change basis K q ell (D.size j) i _ ∈ Submodule.span K
      (basis K q ell (D.size j) i '' {w |
        (if localWindow j i w then (0 : Fin 2) else 1) = 1})
    exact Submodule.subset_span
      ⟨(fun a => x (D.leaves ell L positions ⟨j,a⟩)), if_neg hj, rfl⟩


/-- Complete-word windows on the cells of a partition extract as one tensor
product from their simultaneous global window. The windows may impose arbitrary
frequency bands and grading constraints. -/
private theorem mme_complete_word_cell_windows_product_restriction
    {K : Type u} [Field K] {P : Type v} {C : Type w} [Fintype P]
    (q ell L : ℕ) (positions : Fin L ≃ P) (cell : P → C)
    (D : Partition cell)
    (W : ∀ j : Fin D.parts, Fin 3 → (Fin (D.size j) → CompleteWord ell) → Prop) :
    Restrict
      (kronFin D.parts (fun j =>
        (source K q ell (D.size j)).basisAllAllowedSubtensor
          (basis K q ell (D.size j))
          (fun i x => W j i (label q ell (D.size j) (Equiv.refl _) x))))
      ((source K q ell L).basisAllAllowedSubtensor (basis K q ell L)
        (fun i x => ∀ j, W j i
          (fun r => label q ell L positions x (D.fiber j r).val))) := by
  apply mme_cell_window_product_restriction q ell L positions cell D
  intro i x h j
  have hlabel : label q ell (D.size j) (Equiv.refl _)
      (fun a => x (D.leaves ell L positions ⟨j,a⟩)) =
      (fun r => label q ell L positions x (D.fiber j r).val) := by
    funext r s
    simp [label, Partition.leaves]
  simpa only [hlabel] using h j


private theorem count_fiber {P : Type v} {C W : Type*} [Fintype P]
    {cell : P → C} (D : Partition cell) (f : P → W)
    (j : Fin D.parts) (a : W) :
    MME.RecursiveYZ.count cell f (D.cells j) a =
      MME.RecursiveYZ.count (fun _ : Fin (D.size j) ↦ Unit.unit)
        (fun r ↦ f (D.fiber j r).val) Unit.unit a := by
  classical
  unfold MME.RecursiveYZ.count
  simp only [true_and]
  symm
  apply Finset.card_bij (fun r _ ↦ (D.fiber j r).val)
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact ⟨(D.fiber j r).property, hr⟩
  · intro r hr s hs heq
    exact (D.fiber j).injective (Subtype.ext heq)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    let x : {p : P // cell p = D.cells j} := ⟨p, hp.1⟩
    refine ⟨(D.fiber j).symm x, ?_, ?_⟩
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.apply_symm_apply] using hp.2
    · exact congrArg Subtype.val ((D.fiber j).apply_symm_apply x)


/-- Graded histogram bands on every cell extract simultaneously. Counts in the
cell tensors retain the same normalization as the global histogram, so empty
cells and zero tolerances require no exceptional cases. -/
private theorem mme_graded_histogram_cell_windows_product_restriction
    {K : Type u} [Field K] {P : Type v} {C : Type w} [Fintype P]
    (q ell L : ℕ) (positions : Fin L ≃ P) (cell : P → C)
    (D : Partition cell) (shape : C → Fin 3 → ℕ)
    (center : Fin 3 → C → CompleteWord ell → ℝ) (total eps : ℝ) :
    Restrict
      (kronFin D.parts (fun j =>
        (source K q ell (D.size j)).basisAllAllowedSubtensor
          (basis K q ell (D.size j)) (fun i x =>
            (∀ r, grade (label q ell (D.size j) (Equiv.refl _) x r) = shape (D.cells j) i) ∧
            ∀ a, |(count (fun _ : Fin (D.size j) => Unit.unit)
                (label q ell (D.size j) (Equiv.refl _) x) Unit.unit a : ℝ) / total -
              center i (D.cells j) a| ≤ eps)))
      ((source K q ell L).basisAllAllowedSubtensor (basis K q ell L)
        (fun i x => (∀ p, grade (label q ell L positions x p) = shape (cell p) i) ∧
          ∀ c a, |(count cell (label q ell L positions x) c a : ℝ) / total -
            center i c a| ≤ eps)) := by
  apply mme_cell_window_product_restriction q ell L positions cell D
  intro i x h
  have hlabel (j : Fin D.parts) :
      label q ell (D.size j) (Equiv.refl _)
        (fun a => x (D.leaves ell L positions ⟨j,a⟩)) =
        (fun r => label q ell L positions x (D.fiber j r).val) := by
    funext r s
    simp [label, Partition.leaves]
  constructor
  · intro p
    obtain ⟨⟨j, r⟩, hp⟩ := D.positions.surjective p
    have hg := (h j).1 r
    rw [hlabel] at hg
    change D.positions ⟨j,r⟩ = p at hp
    rw [Partition.positions_apply] at hp
    have hc := (D.fiber j r).property
    simpa only [hp, ← hc] using hg
  · intro c a
    obtain ⟨j, rfl⟩ := D.cells.surjective c
    rw [count_fiber]
    have hh := (h j).2 a
    rw [hlabel] at hh
    exact hh


private theorem histogram_rescale_iff (x center eps total size : ℝ)
    (htotal : 0 < total) (hsize : 0 < size) :
    |x / size - (total / size) * center| ≤ (total / size) * eps ↔
      |x / total - center| ≤ eps := by
  have hid : x / size - (total / size) * center =
      (total / size) * (x / total - center) := by
    field_simp
  rw [hid, abs_mul, abs_of_pos (div_pos htotal hsize)]
  exact mul_le_mul_iff_right₀ (div_pos htotal hsize)

/-- Cell-normalized histogram windows extract from the globally normalized
window after scaling both centers and tolerances by total divided by cell size. -/
private theorem mme_normalized_histogram_cell_windows_product_restriction
    {K : Type u} [Field K] {P : Type v} {C : Type w} [Fintype P]
    (q ell L : ℕ) (positions : Fin L ≃ P) (cell : P → C)
    (D : Partition cell) (shape : C → Fin 3 → ℕ)
    (center : Fin 3 → C → CompleteWord ell → ℝ) (total eps : ℝ)
    (htotal : 0 < total) (hsizes : ∀ j, 0 < D.size j) :
    Restrict
      (kronFin D.parts (fun j =>
        (source K q ell (D.size j)).basisAllAllowedSubtensor
          (basis K q ell (D.size j)) (fun i x =>
            (∀ r, grade (label q ell (D.size j) (Equiv.refl _) x r) = shape (D.cells j) i) ∧
            ∀ a, |(count (fun _ : Fin (D.size j) => Unit.unit)
                (label q ell (D.size j) (Equiv.refl _) x) Unit.unit a : ℝ) / (D.size j : ℝ) -
              (total / (D.size j : ℝ)) * center i (D.cells j) a| ≤
                (total / (D.size j : ℝ)) * eps)))
      ((source K q ell L).basisAllAllowedSubtensor (basis K q ell L)
        (fun i x => (∀ p, grade (label q ell L positions x p) = shape (cell p) i) ∧
          ∀ c a, |(count cell (label q ell L positions x) c a : ℝ) / total -
            center i c a| ≤ eps)) := by
  apply mme_cell_window_product_restriction q ell L positions cell D
  intro i x h
  have hlabel (j : Fin D.parts) :
      label q ell (D.size j) (Equiv.refl _)
        (fun a => x (D.leaves ell L positions ⟨j,a⟩)) =
        (fun r => label q ell L positions x (D.fiber j r).val) := by
    funext r s
    simp [label, Partition.leaves]
  constructor
  · intro p
    obtain ⟨⟨j, r⟩, hp⟩ := D.positions.surjective p
    have hg := (h j).1 r
    rw [hlabel] at hg
    change D.positions ⟨j,r⟩ = p at hp
    rw [Partition.positions_apply] at hp
    have hc := (D.fiber j r).property
    simpa only [hp, ← hc] using hg
  · intro c a
    obtain ⟨j, rfl⟩ := D.cells.surjective c
    rw [count_fiber]
    have hh := (histogram_rescale_iff _ _ eps total (D.size j : ℝ) htotal
      (by exact_mod_cast hsizes j)).mp ((h j).2 a)
    rw [hlabel] at hh
    exact hh



private theorem global_tensor_cast {K : Type u} [Field K] {n m : ℕ} (h : n = m)
    (P : ProfiledCW.Predicate m) :
    ProfiledCW.tensor K (fun i (x : ProfiledCW.FineWord n) =>
      P i (fun j => x (Fin.cast h.symm j))) = ProfiledCW.tensor K P := by
  subst m
  rfl

private theorem global_split_cast {S : Type} {ell L N : ℕ} (p : Fin L ≃ S)
    (h : L * 2 ^ (ell - 1) = N) (x : WordIndex.{u} 5 ell L) :
    ProfiledCW.split p h (fun j => ProfiledCW.fine x (Fin.cast h.symm j)) =
      CWCells.label 5 ell L p x := by
  funext s r
  simp [ProfiledCW.split, CWCells.label, ProfiledCW.fine]

/-- A basis-labelled global window maps into its literal flat profiled tensor. -/
private theorem global_histogram_basis_window_restrict_profiled
    {K : Type u} [Field K] {ell M : ℕ} (D : GlobalCW.HistogramFrame ell M)
    (good : Fin 3 → (Cell D.degree D.R D.bounds → CompleteWord ell → ℕ) → Prop) :
    Restrict
      ((source K 5 ell D.L).basisAllAllowedSubtensor (basis K 5 ell D.L)
        (fun i x => GlobalCW.Graded i D.reference (label 5 ell D.L D.positions x) ∧
          good i (count (GlobalCW.cell D.reference) (label 5 ell D.L D.positions x))))
      (ProfiledCW.tensor K (D.window good)) := by
  classical
  let P := D.window good
  let pull : ProfiledCW.Predicate (D.L * 2 ^ (ell - 1)) :=
    fun i x => P i (fun j => x (Fin.cast D.length.symm j))
  have hmono : Restrict
      ((source K 5 ell D.L).basisAllAllowedSubtensor (basis K 5 ell D.L)
        (fun i x => GlobalCW.Graded i D.reference (label 5 ell D.L D.positions x) ∧
          good i (count (GlobalCW.cell D.reference) (label 5 ell D.L D.positions x))))
      (ProfiledCW.tensor K pull) := by
    apply mme_basis_projected_family_restrict (source K 5 ell D.L)
      (basis K 5 ell D.L) (fun i x => pull i (ProfiledCW.fine x))
      (fun (_ : Fin 1) i x => GlobalCW.Graded i D.reference
        (label 5 ell D.L D.positions x) ∧
        good i (count (GlobalCW.cell D.reference) (label 5 ell D.L D.positions x)))
    · intro j i x hx
      dsimp only [pull, P, GlobalCW.HistogramFrame.window]
      rw [global_split_cast]
      exact hx
    · intro x js _ _
      exact ⟨0, funext (fun i => Fin.eq_zero (js i))⟩
  rw [show ProfiledCW.tensor K pull = ProfiledCW.tensor K P from
    global_tensor_cast D.length P] at hmono
  exact hmono

/-- A global frame's actual profiled histogram window supplies the product of
its graded cell windows with the exact global normalization, including empty cells. -/
private theorem mme_global_frame_histogram_cell_product_restriction
    {K : Type u} [Field K] {ell M : ℕ} (D : GlobalCW.HistogramFrame ell M)
    (E : Partition (GlobalCW.cell D.reference))
    (center : Fin 3 → Cell D.degree D.R D.bounds → CompleteWord ell → ℝ)
    (eps : ℝ) :
    Restrict
      (kronFin E.parts (fun j =>
        (source K 5 ell (E.size j)).basisAllAllowedSubtensor
          (basis K 5 ell (E.size j)) (fun i x =>
            (∀ r, grade (label 5 ell (E.size j) (Equiv.refl _) x r) =
              ((E.cells j).2.val i).val) ∧
            ∀ a, |(count (fun _ : Fin (E.size j) => Unit.unit)
                (label 5 ell (E.size j) (Equiv.refl _) x) Unit.unit a : ℝ) / D.L -
              center i (E.cells j) a| ≤ eps)))
      (ProfiledCW.tensor K (D.window (fun i hist => ∀ c a,
        |(hist c a : ℝ) / D.L - center i c a| ≤ eps))) := by
  have hcell := mme_graded_histogram_cell_windows_product_restriction (K := K)
    5 ell D.L D.positions (GlobalCW.cell D.reference) E
    (fun c i => (c.2.val i).val) center D.L eps
  have hframe := global_histogram_basis_window_restrict_profiled (K := K) D
    (fun i hist => ∀ c a, |(hist c a : ℝ) / D.L - center i c a| ≤ eps)
  exact hcell.trans hframe


private theorem global_frame_cell_card {ell M : ℕ}
    (D : GlobalCW.HistogramFrame ell M) (c : Cell D.degree D.R D.bounds) :
    Fintype.card {p : GlobalCW.Place D.n // GlobalCW.cell D.reference p = c} =
      D.m c.1 c.2 := by
  classical
  rcases c with ⟨r,c⟩
  let e : {p : GlobalCW.Place D.n // GlobalCW.cell D.reference p = ⟨r,c⟩} ≃
      {t : Fin (D.n r) // D.reference r t = c} := {
    toFun := by
      rintro ⟨⟨r',t⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      exact ⟨t, eq_of_heq (Sigma.mk.inj hp).2⟩
    invFun := fun t ↦ ⟨⟨r,t.val⟩, by
      change (⟨r,D.reference r t.val⟩ : Cell D.degree D.R D.bounds) = ⟨r,c⟩
      rw [t.property]⟩
    left_inv := by
      rintro ⟨⟨r',t⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      rfl
    right_inv := by intro t; rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype]
  exact ((Finset.mem_filter.mp D.reference_target).2 r c)

/-- A global frame's actual profiled histogram window supplies the product of
its graded cell windows with the exact global normalization, including empty cells. -/
private theorem mme_global_frame_counted_cell_product_restriction
    {K : Type u} [Field K] {ell M : ℕ} (D : GlobalCW.HistogramFrame ell M)
    {parts : ℕ} (d : Fin parts ≃ Cell D.degree D.R D.bounds)
    (center : Fin 3 → Cell D.degree D.R D.bounds → CompleteWord ell → ℝ)
    (eps : ℝ) :
    Restrict
      (kronFin parts (fun j =>
        (source K 5 ell (D.m (d j).1 (d j).2)).basisAllAllowedSubtensor
          (basis K 5 ell (D.m (d j).1 (d j).2)) (fun i x =>
            (∀ r, grade (label 5 ell (D.m (d j).1 (d j).2) (Equiv.refl _) x r) =
              ((d j).2.val i).val) ∧
            ∀ a, |(count (fun _ : Fin (D.m (d j).1 (d j).2) => Unit.unit)
                (label 5 ell (D.m (d j).1 (d j).2) (Equiv.refl _) x) Unit.unit a : ℝ) / D.L -
              center i (d j) a| ≤ eps)))
      (ProfiledCW.tensor K (D.window (fun i hist => ∀ c a,
        |(hist c a : ℝ) / D.L - center i c a| ≤ eps))) := by
  classical
  let E : Partition (GlobalCW.cell D.reference) := {
    parts := parts
    cells := d
    size := fun j ↦ D.m (d j).1 (d j).2
    fiber := fun j ↦ (Fintype.equivFinOfCardEq (global_frame_cell_card D (d j))).symm }
  exact mme_global_frame_histogram_cell_product_restriction D E center eps


/-- Cell-normalized histogram windows extract from the globally normalized
window after scaling both centers and tolerances by total divided by cell size. -/
private theorem mixed_histogram_cell_windows_product_restriction
    {K : Type u} [Field K] {P : Type v} {C : Type w} [Fintype P]
    (q ell L : ℕ) (positions : Fin L ≃ P) (cell : P → C)
    (D : Partition cell) (shape : C → Fin 3 → ℕ)
    (center : Fin 3 → C → CompleteWord ell → ℝ) (total eps : ℝ)
    (htotal : 0 < total) :
    Restrict
      (kronFin D.parts (fun j =>
        (source K q ell (D.size j)).basisAllAllowedSubtensor
          (basis K q ell (D.size j)) (fun i x =>
            (∀ r, grade (label q ell (D.size j) (Equiv.refl _) x r) = shape (D.cells j) i) ∧
            if D.size j = 0 then ∀ a, |center i (D.cells j) a| ≤ eps else
            ∀ a, |(count (fun _ : Fin (D.size j) => Unit.unit)
                (label q ell (D.size j) (Equiv.refl _) x) Unit.unit a : ℝ) / (D.size j : ℝ) -
              (total / (D.size j : ℝ)) * center i (D.cells j) a| ≤
                (total / (D.size j : ℝ)) * eps)))
      ((source K q ell L).basisAllAllowedSubtensor (basis K q ell L)
        (fun i x => (∀ p, grade (label q ell L positions x p) = shape (cell p) i) ∧
          ∀ c a, |(count cell (label q ell L positions x) c a : ℝ) / total -
            center i c a| ≤ eps)) := by
  classical
  apply mme_cell_window_product_restriction q ell L positions cell D
  intro i x h
  have hlabel (j : Fin D.parts) :
      label q ell (D.size j) (Equiv.refl _)
        (fun a => x (D.leaves ell L positions ⟨j,a⟩)) =
        (fun r => label q ell L positions x (D.fiber j r).val) := by
    funext r s
    simp [label, Partition.leaves]
  constructor
  · intro p
    obtain ⟨⟨j, r⟩, hp⟩ := D.positions.surjective p
    have hg := (h j).1 r
    rw [hlabel] at hg
    change D.positions ⟨j,r⟩ = p at hp
    rw [Partition.positions_apply] at hp
    have hc := (D.fiber j r).property
    simpa only [hp, ← hc] using hg
  · intro c a
    obtain ⟨j, rfl⟩ := D.cells.surjective c
    rw [count_fiber]
    by_cases hz : D.size j = 0
    · haveI : IsEmpty (Fin (D.size j)) := ⟨fun r => by have hr := r.isLt; omega⟩
      have hh := (if_pos hz ▸ (h j).2) a
      simpa [count] using hh
    · have hh := (histogram_rescale_iff _ _ eps total (D.size j : ℝ) htotal
        (by exact_mod_cast Nat.pos_of_ne_zero hz)).mp ((if_neg hz ▸ (h j).2) a)
      rw [hlabel] at hh
      exact hh


/-- Positive cells use their own histogram normalization, with rescaled centers
and tolerances. Empty cells retain exactly the constraint on the global center. -/
private theorem mme_global_frame_normalized_cell_product_restriction
    {K : Type u} [Field K] {ell M : ℕ} (D : GlobalCW.HistogramFrame ell M)
    {parts : ℕ} (d : Fin parts ≃ Cell D.degree D.R D.bounds)
    (center : Fin 3 → Cell D.degree D.R D.bounds → CompleteWord ell → ℝ)
    (eps : ℝ) :
    Restrict
      (kronFin parts (fun j =>
        (source K 5 ell (D.m (d j).1 (d j).2)).basisAllAllowedSubtensor
          (basis K 5 ell (D.m (d j).1 (d j).2)) (fun i x =>
            (∀ r, grade (label 5 ell (D.m (d j).1 (d j).2) (Equiv.refl _) x r) =
              ((d j).2.val i).val) ∧
            if D.m (d j).1 (d j).2 = 0 then ∀ a, |center i (d j) a| ≤ eps else
            ∀ a, |(count (fun _ : Fin (D.m (d j).1 (d j).2) => Unit.unit)
                (label 5 ell (D.m (d j).1 (d j).2) (Equiv.refl _) x) Unit.unit a : ℝ) / (D.m (d j).1 (d j).2 : ℝ) -
              ((D.L : ℝ) / D.m (d j).1 (d j).2) * center i (d j) a| ≤
                ((D.L : ℝ) / D.m (d j).1 (d j).2) * eps)))
      (ProfiledCW.tensor K (D.window (fun i hist => ∀ c a,
        |(hist c a : ℝ) / D.L - center i c a| ≤ eps))) := by
  classical
  let E : Partition (GlobalCW.cell D.reference) := {
    parts := parts
    cells := d
    size := fun j ↦ D.m (d j).1 (d j).2
    fiber := fun j ↦ (Fintype.equivFinOfCardEq (global_frame_cell_card D (d j))).symm }
  have hlength : D.L = D.N + 1 := by
    have h := Fintype.card_congr (D.positions.trans D.hashPositions.symm)
    simpa only [Fintype.card_fin] using h
  have hL : (0 : ℝ) < D.L := by exact_mod_cast (by omega : 0 < D.L)
  have hcell := mixed_histogram_cell_windows_product_restriction (K := K)
    5 ell D.L D.positions (GlobalCW.cell D.reference) E
    (fun c i => (c.2.val i).val) center D.L eps hL
  have hframe := global_histogram_basis_window_restrict_profiled (K := K) D
    (fun i hist => ∀ c a, |(hist c a : ℝ) / D.L - center i c a| ≤ eps)
  exact hcell.trans hframe



/-- Positive cells use their own histogram normalization, with rescaled centers
and tolerances. Empty cells retain exactly the constraint on the global center. -/
private theorem mme_released_global_normalized_cell_product_restriction
    {K : Type u} [Field K] (owner : Fin 6) (k : ℕ) (hk : 0 < k)
    (a : MME.ReleasedGlobal.Reference owner k)
    {parts : ℕ} (d : Fin parts ≃ Cell 8 1 (fun _ _ ↦ 8))
    (eps : ℝ) :
    Restrict
      (kronFin parts (fun j =>
        (source K 5 3 ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2))).basisAllAllowedSubtensor
          (basis K 5 3 ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2))) (fun i x =>
            (∀ r, grade (label 5 3 ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2)) (Equiv.refl _) x r) =
              ((d j).2.val i).val) ∧
            if (k * MME.ReleasedGlobal.coarseCounts owner (d j).2) = 0 then ∀ a, |(MME.ReleasedGlobal.profile owner).2 i (d j) a| ≤ eps else
            ∀ a, |(count (fun _ : Fin ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2)) => Unit.unit)
                (label 5 3 ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2)) (Equiv.refl _) x) Unit.unit a : ℝ) / ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2 : ℕ) : ℝ) -
              ((MME.ReleasedGlobal.blocks k : ℝ) / ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2 : ℕ) : ℝ)) * (MME.ReleasedGlobal.profile owner).2 i (d j) a| ≤
                ((MME.ReleasedGlobal.blocks k : ℝ) / ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2 : ℕ) : ℝ)) * eps)))
      (ProfiledCW.tensor K ((MME.ReleasedGlobal.frame owner k hk a).window
        (MME.ReleasedGlobal.windowGood owner k eps))) := by
  exact mme_global_frame_normalized_cell_product_restriction (K := K)
    (MME.ReleasedGlobal.frame owner k hk a) d (MME.ReleasedGlobal.profile owner).2 eps


/-- Six-symmetrization commutes with finite tensor products, up to actual
mutual restrictions. -/
private theorem mme_sixSymmetrization_kronFin_isomorphic
    {K : Type u} [Field K] {n : ℕ} (T : Fin n → TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.kronFin n (fun i => sixSymmetrization (T i)))
      (sixSymmetrization (TensorObj.kronFin n T)) := by
  rw [← TensorQ.toQ_eq_iff]
  simp only [mme_toQ_kronFin, sixSymmetrization,
    cyclicSymmetrization_eq_public_perm, TensorQ.toQ_kron,
    ← TensorQ.permAut_toQ, map_prod, map_mul, Finset.prod_mul_distrib]


private theorem six_product_exponential_extraction
    {K : Type u} [Field K] {n : ℕ} (T : Fin n → TensorObj K 3)
    (tau : ℝ) (rate : Fin n → ℝ)
    (hextract : ∀ i, ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
        (sixSymmetrization (T i)) ∧
      Real.exp (rate i) ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ), 0 < q ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
        (sixSymmetrization (TensorObj.kronFin n T)) ∧
      Real.exp (∑ i, rate i) ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨q, a, b, c, hrestrict, hweight⟩ :=
    mme_finite_MM_extractions_kronFin_tau_product
      (fun i => sixSymmetrization (T i)) tau (fun i => Real.exp (rate i))
      (fun i => (Real.exp_pos _).le) hextract
  have hweight' : Real.exp (∑ i, rate i) ≤
      ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
    simpa only [Real.exp_sum] using hweight
  have hq : 0 < q := by
    by_contra h
    have hz : q = 0 := by omega
    subst q
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hweight'
    exact (Real.exp_pos _).not_ge hweight'
  exact ⟨q, a, b, c, hq,
    hrestrict.trans (mme_sixSymmetrization_kronFin_isomorphic T).1, hweight'⟩



/-- Matrix extractions at a common global replication combine across every
normalized cell, retaining the sum of their logarithmic weight bounds in the
actual global histogram tensor. -/
theorem solution
    {K : Type u} [Field K] (owner : Fin 6) (k : ℕ) (hk : 0 < k)
    (reference : MME.ReleasedGlobal.Reference owner k)
    {parts : ℕ} (d : Fin parts ≃ Cell 8 1 (fun _ _ ↦ 8))
    (eps tau : ℝ) (rate : Fin parts → ℝ) :
    let cell := fun j : Fin parts =>
        (source K 5 3 ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2))).basisAllAllowedSubtensor
          (basis K 5 3 ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2))) (fun i x =>
            (∀ r, grade (label 5 3 ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2)) (Equiv.refl _) x r) =
              ((d j).2.val i).val) ∧
            if (k * MME.ReleasedGlobal.coarseCounts owner (d j).2) = 0 then ∀ a, |(MME.ReleasedGlobal.profile owner).2 i (d j) a| ≤ eps else
            ∀ a, |(count (fun _ : Fin ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2)) => Unit.unit)
                (label 5 3 ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2)) (Equiv.refl _) x) Unit.unit a : ℝ) / ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2 : ℕ) : ℝ) -
              ((MME.ReleasedGlobal.blocks k : ℝ) / ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2 : ℕ) : ℝ)) * (MME.ReleasedGlobal.profile owner).2 i (d j) a| ≤
                ((MME.ReleasedGlobal.blocks k : ℝ) / ((k * MME.ReleasedGlobal.coarseCounts owner (d j).2 : ℕ) : ℝ)) * eps)
    (∀ j, ∃ (copies : ℕ) (a b c : Fin copies → ℕ),
      Restrict (bigAdd (fun v => MMObj K (a v) (b v) (c v)))
        (sixSymmetrization (cell j)) ∧
      Real.exp (rate j) ≤ ∑ v, ((a v * b v * c v : ℕ) : ℝ) ^ tau) →
    ∃ (copies : ℕ) (a b c : Fin copies → ℕ), 0 < copies ∧
      Restrict (bigAdd (fun v => MMObj K (a v) (b v) (c v)))
        (sixSymmetrization (ProfiledCW.tensor K
          ((MME.ReleasedGlobal.frame owner k hk reference).window
            (MME.ReleasedGlobal.windowGood owner k eps)))) ∧
      Real.exp (∑ j, rate j) ≤ ∑ v, ((a v * b v * c v : ℕ) : ℝ) ^ tau := by
  classical
  dsimp only
  intro hextract
  obtain ⟨copies, a, b, c, hpos, hproduct, hweight⟩ :=
    six_product_exponential_extraction _ tau rate hextract
  have hwindow := mme_released_global_normalized_cell_product_restriction
    (K := K) owner k hk reference d eps
  exact ⟨copies, a, b, c, hpos,
    hproduct.trans (mme_sixSymmetrization_restrict hwindow), hweight⟩


#print axioms solution
