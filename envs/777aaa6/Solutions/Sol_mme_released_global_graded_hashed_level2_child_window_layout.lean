-- Prove2me | solution 1 for mme_released_global_graded_hashed_level2_child_window_layout
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T20:07:55.735218+00:00
-- url     : https://prove2.me/submissions/26f69b07-ecd4-4158-9624-8ea224e7ab91

import Definitions.Def_mme_released_global_two_part_split_data
import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_released_positive_integer_frame_data
import Definitions.Def_mme_regional_tolerance_window_data
import Definitions.Def_mme_dwz_profiled_regional_positions_data
import Theorems.Thm_mme_released_positive_integer_frame
import Theorems.Thm_mme_released_global_supported_frame
import Theorems.Thm_mme_released_level2_level3_positive_cell_correspondence
open BigOperators Filter MME MME.ProfiledCW MME.GlobalCW MME.RecursiveYZ MME.CompleteSplit
  MME.ReleasedGlobal MME.RegionRealization MME.ReleasedRecursive.Asm MME.DWZProfiledRegional
open scoped Classical
set_option autoImplicit false

namespace C9Layout

/-- Counting a fibre of a sigma-type map that keeps the index. -/
theorem card_sigma_fibre {ι : Type} [DecidableEq ι] [Fintype ι] {A C : ι → Type}
    [∀ i, Fintype (A i)] (g : ∀ i, A i → C i) (Q : (Σ i, A i) → Prop)
    (ρ : ι) (c : C ρ) :
    Fintype.card {s : Σ i, A i // (⟨s.1, g s.1 s.2⟩ : Σ i, C i) = ⟨ρ, c⟩ ∧ Q s} =
      Fintype.card {x : A ρ // g ρ x = c ∧ Q ⟨ρ, x⟩} := by
  rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card_filter, Finset.card_filter,
    Fintype.sum_sigma]
  rw [Finset.sum_eq_single ρ]
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp only [Sigma.mk.inj_iff, heq_iff_eq, true_and]
  · intro b _ hb
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hb (Sigma.mk.inj_iff.1 h).1
  · intro h; exact absurd (Finset.mem_univ _) h

theorem card_eq_of_inst {α : Type} (i1 i2 : Fintype α) :
    @Fintype.card α i1 = @Fintype.card α i2 := by
  congr
  exact Subsingleton.elim _ _

theorem count_eq_card {P C W : Type} [Fintype P] (cell : P → C) (f : P → W) (c : C) (w : W) :
    RecursiveYZ.count cell f c w = Fintype.card {p // cell p = c ∧ f p = w} := by
  classical
  unfold RecursiveYZ.count
  rw [Fintype.card_subtype]

theorem card_fibre_sum {S W : Type} [Fintype S] [Fintype W] [DecidableEq W] (P : S → Prop)
    (f : S → W) :
    ∑ v, Fintype.card {s // P s ∧ f s = v} = Fintype.card {s // P s} := by
  classical
  rw [Fintype.card_subtype, Finset.card_eq_sum_card_fiberwise
    (f := f) (t := Finset.univ) (by intro x _; exact Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [Fintype.card_subtype, Finset.filter_filter]

/-- Positions of a recursive address in one cell: both halves are counted. -/
theorem card_fullCell {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (a : RecursiveXHash.Address half R parent n) (ha : a ∈ RecursiveXHash.target m)
    (c : Cell half R parent) :
    Fintype.card {p : Position n // fullCell htotal a p = c} =
      m c.1 c.2 + m c.1 (complement (htotal c.1) c.2) := by
  obtain ⟨ρ, s⟩ := c
  have hj : ∀ r, RecursiveThinSplit.HasJointCounts (a r) (m r) := by
    simpa [RecursiveXHash.target] using ha
  have h1 := card_sigma_fibre (A := fun r ↦ Fin (n r) × Fin 2)
    (fun r x ↦ if x.2 = 0 then a r x.1 else complement (htotal r) (a r x.1))
    (fun _ ↦ True) ρ s
  simp only [and_true] at h1
  refine (h1 : _).trans ?_
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fin.isValue, if_true, one_ne_zero, if_false]
  rw [Finset.sum_add_distrib, ← hj ρ s, ← hj ρ (complement (htotal ρ) s)]
  simp only [RecursiveThinSplit.count, Finset.card_filter]
  congr 1
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  have : complement (htotal ρ) (a ρ t) = s ↔ a ρ t = complement (htotal ρ) s := by
    constructor
    · rintro rfl; rw [complement_complement]
    · rintro h; rw [h, complement_complement]
  simp only [this]



theorem layout_generic
    (K : ℕ)
    (parent3 : Fin 6 → Fin 88 → Fin 3 → ℕ)
    (htotal3 : ∀ ρ r, parent3 ρ r 0 + parent3 ρ r 1 + parent3 ρ r 2 = 2 * (2 * 2 ^ (2 - 1)))
    (n3 : Fin 6 → Fin 88 → ℕ)
    (m3 : ∀ ρ r, RecursiveThinSplit.Split (2 * 2 ^ (2 - 1)) (parent3 ρ r) → ℕ)
    (mu3 : ∀ ρ, Fin 3 → Cell (2 * 2 ^ (2 - 1)) 88 (parent3 ρ) → CompleteWord 2 → ℕ)
    (R2 : ℕ) (parent2 : Fin R2 → Fin 3 → ℕ)
    (htotal2 : ∀ r, parent2 r 0 + parent2 r 1 + parent2 r 2 = 2 * (2 * 2 ^ (1 - 1)))
    (n2 : Fin R2 → ℕ) (m2 : ∀ r, RecursiveThinSplit.Split (2 * 2 ^ (1 - 1)) (parent2 r) → ℕ)
    (mu2 : Fin 3 → Cell (2 * 2 ^ (1 - 1)) R2 parent2 → CompleteWord 1 → ℕ)
    (σ : Fin 6 → Equiv.Perm (Fin 3))
    (B : Fin 6 → ℕ)
    (F : ∀ ρ, Fin (B ρ * 2) ≃ Position (fun r ↦ K * n3 ρ r))
    (len : ∀ ρ, (B ρ * 2) * 2 ^ (2 - 1) = B ρ * 4)
    (ref : ∀ ρ, RecursiveXHash.Address (2 * 2 ^ (2 - 1)) 88 (parent3 ρ) (fun r ↦ K * n3 ρ r))
    (href : ∀ ρ, ref ρ ∈ RecursiveXHash.target (fun r c ↦ K * m3 ρ r c))
    (hmass : ∀ ρ i (c : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 ρ)), (∑ w, K * mu3 ρ i c w) =
      K * m3 ρ c.1 c.2 + K * m3 ρ c.1 (complement (htotal3 ρ c.1) c.2))
    (φ : Fin R2 → (ρ : Fin 6) × Cell (2 * 2 ^ (2 - 1)) 88 (parent3 ρ))
    (D1 : Function.Injective φ)
    (D2 : ∀ r j, ((φ r).2.2.val j).val ≠ 0)
    (D3 : ∀ ρ (c : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 ρ)), (∀ j, (c.2.val j).val ≠ 0) →
      0 < m3 ρ c.1 c.2 + m3 ρ c.1 (complement (htotal3 ρ c.1) c.2) → ∃ r, φ r = ⟨ρ, c⟩)
    (D4 : ∀ r, n2 r = m3 (φ r).1 (φ r).2.1 (φ r).2.2 +
      m3 (φ r).1 (φ r).2.1 (complement (htotal3 (φ r).1 (φ r).2.1) (φ r).2.2))
    (D5 : ∀ r i, parent2 r i = ((φ r).2.2.val ((σ (φ r).1).symm i)).val)
    (D6 : ∀ r i (w : CompleteWord 2),
      parentMixture htotal2 (fun r ↦ K * n2 r) (fun r c ↦ K * m2 r c) (fun c w ↦ K * mu2 i c w) r
        (fun h _ ↦ w h) =
      cellFrequency (fun c w ↦ K * mu3 (φ r).1 ((σ (φ r).1).symm i) c w) (φ r).2 w)
    (N : ℕ) (E : ((r : Fin 6) × Fin (B r * 4)) ≃ Fin N)
    (τ δ : ℝ) (hτ : τ ≤ δ) (hδ : 0 ≤ δ) :
    ∃ (L : ℕ) (zc : Fin L → (ρ : Fin 6) ×
        {c : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 ρ) // ∃ j, (c.2.val j).val = 0}),
      (∀ z, Fintype.card {p : Fin L // zc p = z} =
        K * (m3 z.1 z.2.1.1 z.2.1.2 + m3 z.1 z.2.1.1 (complement (htotal3 z.1 z.2.1.1) z.2.1.2))) ∧
      ∃ pos : (Fin (lenAt n2 K * 2 ^ (1 - 1)) ⊕ Fin (L * 2 ^ (2 - 1))) ≃ Fin N,
        ∀ (i : Fin 3) (y : FineWord N),
          (ParentGraded parent2 (fun r ↦ K * n2 r) i
              (ProfiledCW.split (ell := 1) (positionsAt n2 K) rfl (fun q ↦ y (pos (Sum.inl q)))) ∧
            parentTypical htotal2 (fun r ↦ K * n2 r) (fun r c ↦ K * m2 r c)
              (fun c w ↦ K * mu2 i c w) τ
              (ProfiledCW.split (ell := 1) (positionsAt n2 K) rfl (fun q ↦ y (pos (Sum.inl q))))) →
          ((∀ p, CWCells.grade (ProfiledCW.split (ell := 2) (Equiv.refl (Fin L)) rfl
                (fun q ↦ y (pos (Sum.inr q))) p) =
              ((zc p).2.1.2.val ((σ (zc p).1).symm i)).val) ∧
            Useful zc (fun z w ↦ K * mu3 z.1 ((σ z.1).symm i) z.2.1 w)
              (ProfiledCW.split (ell := 2) (Equiv.refl (Fin L)) rfl
                (fun q ↦ y (pos (Sum.inr q))))) →
          ∀ r : Fin 6,
            RecursiveYZ.Graded (htotal3 r) ((σ r).symm i) (ref r)
              (ProfiledCW.split (ell := 2) (F r) (len r) (fun q ↦ y (E ⟨r, q⟩))) ∧
            ∀ c w, |cellFrequency (RecursiveYZ.count (fullCell (htotal3 r) (ref r))
                (ProfiledCW.split (ell := 2) (F r) (len r) (fun q ↦ y (E ⟨r, q⟩)))) c w -
              cellFrequency (fun c w ↦ K * mu3 r ((σ r).symm i) c w) c w| ≤ δ := by
  classical
  -- level-three slots and their cells
  let Slot := (ρ : Fin 6) × Position (fun r ↦ K * n3 ρ r)
  let key : Slot → (ρ : Fin 6) × Cell (2 * 2 ^ (2 - 1)) 88 (parent3 ρ) :=
    fun s ↦ ⟨s.1, fullCell (htotal3 s.1) (ref s.1) s.2⟩
  have hcard : ∀ z, Fintype.card {s : Slot // key s = z} =
      K * (m3 z.1 z.2.1 z.2.2 + m3 z.1 z.2.1 (complement (htotal3 z.1 z.2.1) z.2.2)) := by
    rintro ⟨ρ, c⟩
    have h := card_sigma_fibre (A := fun ρ ↦ Position (fun r ↦ K * n3 ρ r))
      (fun ρ p ↦ fullCell (htotal3 ρ) (ref ρ) p) (fun _ ↦ True) ρ c
    simp only [and_true] at h
    rw [mul_add, ← card_fullCell (htotal3 ρ) _ (ref ρ) (href ρ) c]
    exact h
  let Pos : Slot → Prop := fun s ↦ ∃ r2, φ r2 = key s
  have hnotpos : ∀ s, (∃ j, ((key s).2.2.val j).val = 0) → ¬ Pos s := by
    rintro s ⟨j, hj⟩ ⟨r2, hr2⟩
    have := D2 r2 j
    rw [hr2] at this
    exact this hj
  have hzero : ∀ s, ¬ Pos s → ∃ j, ((key s).2.2.val j).val = 0 := by
    intro s hs
    by_contra h
    push_neg at h
    apply hs
    have hpos : 0 < Fintype.card {s' : Slot // key s' = key s} :=
      Fintype.card_pos_iff.2 ⟨⟨s, rfl⟩⟩
    rw [hcard] at hpos
    exact D3 (key s).1 (key s).2 h (Nat.pos_of_mul_pos_left hpos)
  -- the positive slots, fibred over the level-two types
  let κ : {s : Slot // Pos s} → Fin R2 := fun x ↦ x.2.choose
  have hκ : ∀ x, φ (κ x) = key x.1 := fun x ↦ x.2.choose_spec
  have hκiff : ∀ x r2, κ x = r2 ↔ key x.1 = φ r2 := by
    intro x r2
    constructor
    · rintro rfl; exact (hκ x).symm
    · intro h; exact D1 ((hκ x).trans h)
  have hcP : ∀ r2, Fintype.card {x : {s : Slot // Pos s} // κ x = r2} = K * n2 r2 := by
    intro r2
    rw [D4 r2, ← hcard (φ r2)]
    exact Fintype.card_congr
      { toFun := fun x ↦ ⟨x.1.1, (hκiff _ _).1 x.2⟩
        invFun := fun s ↦ ⟨⟨s.1, r2, s.2.symm⟩, (hκiff ⟨s.1, r2, s.2.symm⟩ r2).2 s.2⟩
        left_inv := fun x ↦ rfl
        right_inv := fun s ↦ rfl }
  obtain ⟨eP⟩ : Nonempty (∀ r2, Fin (K * n2 r2) ≃ {x : {s : Slot // Pos s} // κ x = r2}) :=
    ⟨fun r2 ↦ Fintype.equivOfCardEq (by rw [Fintype.card_fin, hcP])⟩
  -- the zero slots
  obtain ⟨eZ⟩ : Nonempty (Fin (Fintype.card {s : Slot // ¬ Pos s}) ≃ {s : Slot // ¬ Pos s}) :=
    ⟨(Fintype.equivFin _).symm⟩
  set L := Fintype.card {s : Slot // ¬ Pos s} with hL
  let zc : Fin L → (ρ : Fin 6) ×
      {c : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 ρ) // ∃ j, (c.2.val j).val = 0} :=
    fun q ↦ ⟨(key (eZ q).1).1, ⟨(key (eZ q).1).2, hzero _ (eZ q).2⟩⟩
  have hzc : ∀ q z, zc q = z ↔ key (eZ q).1 = ⟨z.1, z.2.1⟩ := by
    intro q z
    obtain ⟨z1, z2, hz2⟩ := z
    constructor
    · rintro h; rw [← h]
    · intro h
      simp only [zc]
      simp only [key] at h ⊢
      obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 h
      subst h1
      rw [heq_iff_eq] at h2
      subst h2
      rfl
  -- the bijection
  have hlen1 : lenAt n2 K * 2 ^ (1 - 1) = lenAt n2 K := by simp
  let A : Fin (lenAt n2 K * 2 ^ (1 - 1)) ≃ {s : Slot // Pos s} × Fin 2 :=
    (finCongr hlen1).trans ((positionsAt n2 K).trans
      ((Equiv.sigmaProdDistrib (fun r2 ↦ Fin (K * n2 r2)) (Fin 2)).symm.trans
        (Equiv.prodCongr ((Equiv.sigmaCongrRight eP).trans (Equiv.sigmaFiberEquiv κ))
          (Equiv.refl _))))
  let Bz : Fin (L * 2 ^ (2 - 1)) ≃ {s : Slot // ¬ Pos s} × Fin 2 :=
    finProdFinEquiv.symm.trans (Equiv.prodCongr eZ (Equiv.refl _))
  let lt : Slot × Fin 2 ≃ ((r : Fin 6) × Fin (B r * 4)) :=
    (Equiv.sigmaProdDistrib _ _).trans (Equiv.sigmaCongrRight fun ρ ↦
      (Equiv.prodCongr (F ρ).symm (Equiv.refl (Fin 2))).trans
        (finProdFinEquiv.trans (finCongr (len ρ))))
  let pos : (Fin (lenAt n2 K * 2 ^ (1 - 1)) ⊕ Fin (L * 2 ^ (2 - 1))) ≃ Fin N :=
    (Equiv.sumCongr A Bz).trans ((Equiv.sumProdDistrib _ _ _).symm.trans
      ((Equiv.prodCongr (Equiv.sumCompl Pos) (Equiv.refl _)).trans (lt.trans E)))
  let word : FineWord N → Slot → CompleteWord 2 := fun y s j ↦ y (E (lt (s, j)))
  have hE1 : ∀ (y : FineWord N) r2 t h, ProfiledCW.split (ell := 1) (positionsAt n2 K) rfl
      (fun q ↦ y (pos (Sum.inl q))) ⟨r2, t, h⟩ = fun _ ↦ y (E (lt ((eP r2 t).1.1, h))) := by
    intro y r2 t h
    funext r0
    have hfc : finCongr hlen1 (Fin.cast rfl (finProdFinEquiv
        ((positionsAt n2 K).symm ⟨r2, t, h⟩, r0))) = (positionsAt n2 K).symm ⟨r2, t, h⟩ := by
      ext
      have := r0.isLt
      simp only [pow_zero, tsub_self] at this
      simp [finProdFinEquiv]
    simp only [ProfiledCW.split, pos, A, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, hfc]
    simp
  have hE2 : ∀ (y : FineWord N) q, ProfiledCW.split (ell := 2) (Equiv.refl (Fin L)) rfl
      (fun q ↦ y (pos (Sum.inr q))) q = word y (eZ q).1 := by
    intro y q
    funext j
    simp [ProfiledCW.split, pos, Bz, word]
  have hE3 : ∀ (y : FineWord N) r, ProfiledCW.split (ell := 2) (F r) (len r) (fun q ↦ y (E ⟨r, q⟩)) =
      fun p ↦ word y ⟨r, p⟩ := fun y r ↦ rfl
  refine ⟨L, zc, ?_, pos, ?_⟩
  · intro z
    have h1 : Fintype.card {q : Fin L // zc q = z} =
        Fintype.card {s : Slot // key s = ⟨z.1, z.2.1⟩} := by
      refine Fintype.card_congr ((Equiv.subtypeEquiv
        (q := fun x : {s : Slot // ¬ Pos s} ↦ key x.1 = ⟨z.1, z.2.1⟩) eZ
        (fun q ↦ hzc q z)).trans ?_)
      exact
        { toFun := fun x ↦ ⟨x.1.1, x.2⟩
          invFun := fun s ↦ ⟨⟨s.1, hnotpos s.1 (by rw [s.2]; exact z.2.2)⟩, s.2⟩
          left_inv := fun x ↦ rfl
          right_inv := fun s ↦ rfl }
    rw [h1, hcard]
  rintro i y ⟨hPG, hPT⟩ ⟨hZg, hZU⟩ r
  rw [hE3 y r]
  have hcnt : ∀ (c : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 r)) w,
      RecursiveYZ.count (fullCell (htotal3 r) (ref r)) (fun p ↦ word y ⟨r, p⟩) c w =
        Fintype.card {s : Slot // key s = ⟨r, c⟩ ∧ word y s = w} := by
    intro c w
    have h := card_sigma_fibre (A := fun ρ ↦ Position (fun r ↦ K * n3 ρ r))
      (fun ρ p ↦ fullCell (htotal3 ρ) (ref ρ) p) (fun s ↦ word y s = w) r c
    rw [count_eq_card]
    exact (card_eq_of_inst _ _).trans (h.symm.trans (card_eq_of_inst _ _))
  have hsum : ∀ (c : Cell (2 * 2 ^ (2 - 1)) 88 (parent3 r)),
      ∑ v, RecursiveYZ.count (fullCell (htotal3 r) (ref r)) (fun p ↦ word y ⟨r, p⟩) c v =
        K * (m3 r c.1 c.2 + m3 r c.1 (complement (htotal3 r c.1) c.2)) := by
    intro c
    simp only [hcnt]
    rw [← hcard ⟨r, c⟩]
    refine Eq.trans ?_ ((card_fibre_sum (fun s ↦ key s = ⟨r, c⟩) (word y)).trans
      (card_eq_of_inst _ _))
    exact Finset.sum_congr rfl fun v _ ↦ card_eq_of_inst _ _
  refine ⟨fun p ↦ ?_, fun c w ↦ ?_⟩
  · show ∑ j, (word y ⟨r, p⟩ j).val =
      ((fullCell (htotal3 r) (ref r) p).2.val ((σ r).symm i)).val
    by_cases hs : Pos ⟨r, p⟩
    · set x : {s : Slot // Pos s} := ⟨⟨r, p⟩, hs⟩ with hx
      set t := (eP (κ x)).symm ⟨x, rfl⟩ with ht_def
      have ht : (eP (κ x) t).1.1 = ⟨r, p⟩ := by simp [t, x]
      have h := hPG (κ x) t
      rw [hE1, hE1, ht, D5, hκ x] at h
      simp only [CWCells.grade, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        pow_zero, tsub_self, one_smul] at h
      show ∑ j : Fin 2, (word y ⟨r, p⟩ j).val = _
      rw [Fin.sum_univ_two]
      exact h
    · set q := eZ.symm ⟨⟨r, p⟩, hs⟩ with hq_def
      have hq : eZ q = ⟨⟨r, p⟩, hs⟩ := by simp [q]
      have h : CWCells.grade (word y (eZ q).1) =
          (((key (eZ q).1).2.2.val) ((σ (key (eZ q).1).1).symm i)).val := by
        have := hZg q
        rw [hE2] at this
        exact this
      rw [hq] at h
      exact h
  · by_cases hz : ∃ j, (c.2.val j).val = 0
    · have hU : ∀ v, RecursiveYZ.count (fullCell (htotal3 r) (ref r))
          (fun p ↦ word y ⟨r, p⟩) c v = K * mu3 r ((σ r).symm i) c v := by
        intro v
        rw [hcnt]
        refine Eq.trans ?_ (hZU ⟨r, ⟨c, hz⟩⟩ v)
        rw [count_eq_card]
        simp only [hE2]
        symm
        refine Fintype.card_congr ((Equiv.subtypeEquiv
          (q := fun x : {s : Slot // ¬ Pos s} ↦ key x.1 = ⟨r, c⟩ ∧ word y x.1 = v) eZ
          (fun q ↦ ?_)).trans ?_)
        · rw [hzc]
        · exact
            { toFun := fun x ↦ ⟨x.1.1, x.2⟩
              invFun := fun s ↦ ⟨⟨s.1, hnotpos s.1 (by rw [s.2.1]; exact hz)⟩, s.2⟩
              left_inv := fun x ↦ rfl
              right_inv := fun s ↦ rfl }
      simp only [cellFrequency, hU, sub_self, abs_zero]
      exact hδ
    · push_neg at hz
      by_cases hex : ∃ r2, φ r2 = ⟨r, c⟩
      · obtain ⟨r2, hr2⟩ := hex
        have hT := hPT r2 (fun h _ ↦ w h)
        rw [D6] at hT
        have hn := D4 r2
        rw [hr2] at hT hn
        have hc1 : ∀ inst : Fintype {t : Fin (K * n2 r2) // ∀ h, ProfiledCW.split (ell := 1)
            (positionsAt n2 K) rfl (fun q ↦ y (pos (Sum.inl q))) ⟨r2, t, h⟩ = fun _ ↦ w h},
            @Fintype.card _ inst =
            RecursiveYZ.count (fullCell (htotal3 r) (ref r)) (fun p ↦ word y ⟨r, p⟩) c w := by
          intro inst
          refine (card_eq_of_inst inst inferInstance).trans ?_
          rw [hcnt]
          refine Fintype.card_congr ((Equiv.subtypeEquiv
            (q := fun x : {x : {s : Slot // Pos s} // κ x = r2} ↦ word y x.1.1 = w) (eP r2)
            (fun t ↦ ?_)).trans ?_)
          · simp only [hE1]
            constructor
            · intro H
              funext j
              exact congrFun (H j) ⟨0, by norm_num⟩
            · intro H h
              funext _
              rw [← H]
          · exact
              { toFun := fun x ↦ ⟨x.1.1.1, ((hκiff _ _).1 x.1.2).trans hr2, x.2⟩
                invFun := fun s ↦ ⟨⟨⟨s.1, r2, hr2.trans s.2.1.symm⟩,
                  (hκiff ⟨s.1, r2, hr2.trans s.2.1.symm⟩ r2).2 (s.2.1.trans hr2.symm)⟩, s.2.2⟩
                left_inv := fun x ↦ rfl
                right_inv := fun s ↦ rfl }
        have hc2 : ∑ v, RecursiveYZ.count (fullCell (htotal3 r) (ref r))
            (fun p ↦ word y ⟨r, p⟩) c v = K * n2 r2 := by
          rw [hsum, hn]
        rw [hc1] at hT
        simp only [cellFrequency] at hT ⊢
        rw [hc2]
        exact le_of_lt (lt_of_lt_of_le hT hτ)
      · have hm : m3 r c.1 c.2 + m3 r c.1 (complement (htotal3 r c.1) c.2) = 0 := by
          by_contra h0
          exact hex (D3 r c hz (Nat.pos_of_ne_zero h0))
        have h0 : ∀ v, RecursiveYZ.count (fullCell (htotal3 r) (ref r))
            (fun p ↦ word y ⟨r, p⟩) c v = 0 := by
          intro v
          have := hsum c
          rw [hm, mul_zero, Finset.sum_eq_zero_iff] at this
          exact this v (Finset.mem_univ _)
        have h0' : ∀ v, K * mu3 r ((σ r).symm i) c v = 0 := by
          intro v
          have := hmass r ((σ r).symm i) c
          rw [← mul_add, hm, mul_zero, Finset.sum_eq_zero_iff] at this
          exact this v (Finset.mem_univ _)
        simp only [cellFrequency, h0, h0', Nat.cast_zero, zero_div, sub_self, abs_zero]
        exact hδ


theorem cellFrequency_scale {C W : Type} [Fintype W] (K : ℕ) (hK : 0 < K) (mu : C → W → ℕ)
    (c : C) (w : W) :
    cellFrequency (fun c w ↦ K * mu c w) c w = cellFrequency mu c w := by
  unfold cellFrequency
  rw [← Finset.mul_sum]
  push_cast
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  rw [mul_div_mul_left _ _ hK']

theorem parentMixture_scale {half R : ℕ} {W : Type} [Fintype W] {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ) (K : ℕ) (hK : 0 < K) (r : Fin R) (w : Fin 2 → W) :
    parentMixture htotal (fun r ↦ K * n r) (fun r c ↦ K * m r c) (fun c w ↦ K * mu c w) r w =
      parentMixture htotal n m mu r w := by
  unfold parentMixture
  simp only [cellFrequency_scale K hK]
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  push_cast
  simp only [mul_assoc]
  rw [← Finset.mul_sum, mul_div_mul_left _ _ hK']

theorem tolerance_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, 0 < k ∧ Real.sqrt (8 * (25 * (1104 : ℝ) *
      (Fintype.card (CompleteSplit.CompleteWord 1) : ℝ) ^ 2) *
      ((Nat.sqrt (k^2) + 2 : ℕ) : ℝ) / (k^2 : ℕ)) ≤ δ := by
  set C : ℝ := 8 * (25 * (1104 : ℝ) * (Fintype.card (CompleteSplit.CompleteWord 1) : ℝ) ^ 2)
    with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  filter_upwards [eventually_ge_atTop (max 1 ⌈3 * C / δ ^ 2⌉₊)] with k hk
  have hk1 : 1 ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : 3 * C / δ ^ 2 ≤ (k : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hk)
  refine ⟨hk1, ?_⟩
  rw [Nat.sqrt_eq' k]
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hδ2 : 0 < δ ^ 2 := by positivity
  have h3 : 3 * C ≤ δ ^ 2 * k := by
    rw [div_le_iff₀ hδ2] at hk2; linarith
  have hkey : C * ((k + 2 : ℕ) : ℝ) / ((k ^ 2 : ℕ) : ℝ) ≤ δ ^ 2 := by
    push_cast
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  calc Real.sqrt (C * ((k + 2 : ℕ) : ℝ) / ((k ^ 2 : ℕ) : ℝ)) ≤ Real.sqrt (δ ^ 2) :=
        Real.sqrt_le_sqrt hkey
    _ = δ := Real.sqrt_sq hδ.le

end C9Layout

open C9Layout in
theorem solution :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ k : ℕ in atTop,
      ∃ (a : ∀ o : Fin 6, Reference o (k^2))
        (frame : ∀ r : Fin 6, ReleasedPositiveInteger.Frame r (k^2)),
      ∀ E : ((r : Fin 6) × Fin (ReleasedJointInterior.blocks r (k^2) * 4)) ≃
          Fin (partSize (k^2) a 1),
      ∃ (L : ℕ) (zc : Fin L → (ρ : Fin 6) × {c : Cell (2 * 2 ^ (2 - 1)) 88 (RecStage.parent3 ρ) //
          ∃ j, (c.2.val j).val = 0}),
        (∀ z, Fintype.card {p : Fin L // zc p = z} =
          k^2 * (RecStage.m3 z.1 z.2.1.1 z.2.1.2 +
            RecStage.m3 z.1 z.2.1.1 (complement (RecStage.htotal3 z.1 z.2.1.1) z.2.1.2))) ∧
        ∃ pos : (Fin (lenAt RecStage.n2 (k^2) * 2 ^ (1 - 1)) ⊕ Fin (L * 2 ^ (2 - 1))) ≃
            Fin (partSize (k^2) a 1),
          ∀ (i : Fin 3) (y : FineWord (partSize (k^2) a 1)),
            (ParentGraded RecStage.parent2 (fun r ↦ k^2 * RecStage.n2 r) i
                (ProfiledCW.split (ell := 1) (positionsAt RecStage.n2 (k^2)) rfl
                  (fun q ↦ y (pos (Sum.inl q)))) ∧
              parentTypical RecStage.htotal2 (fun r ↦ k^2 * RecStage.n2 r)
                (fun r c ↦ k^2 * RecStage.m2 r c) (fun c w ↦ k^2 * RecStage.mu2 i c w)
                (Real.sqrt (8 * (25 * (1104 : ℝ) *
                  (Fintype.card (CompleteSplit.CompleteWord 1) : ℝ) ^ 2) *
                  ((Nat.sqrt (k^2) + 2 : ℕ) : ℝ) / (k^2 : ℕ)))
                (ProfiledCW.split (ell := 1) (positionsAt RecStage.n2 (k^2)) rfl
                  (fun q ↦ y (pos (Sum.inl q))))) →
            ((∀ p, CWCells.grade (ProfiledCW.split (ell := 2) (Equiv.refl (Fin L)) rfl
                  (fun q ↦ y (pos (Sum.inr q))) p) =
                ((zc p).2.1.2.val ((ReleasedJointInterior.roleEquiv (zc p).1).symm i)).val) ∧
              Useful zc (fun z w ↦ k^2 * RecStage.mu3 z.1
                  ((ReleasedJointInterior.roleEquiv z.1).symm i) z.2.1 w)
                (ProfiledCW.split (ell := 2) (Equiv.refl (Fin L)) rfl
                  (fun q ↦ y (pos (Sum.inr q))))) →
            ∀ r : Fin 6,
              RecursiveYZ.Graded (RecStage.htotal3 r) ((ReleasedJointInterior.roleEquiv r).symm i)
                (frame r).reference
                (ProfiledCW.split (ell := 2) (frame r).positions
                  (ReleasedJointInterior.positions_length r (k^2)) (fun q ↦ y (E ⟨r, q⟩))) ∧
              ∀ c w, |cellFrequency (RecursiveYZ.count (fullCell (RecStage.htotal3 r) (frame r).reference)
                  (ProfiledCW.split (ell := 2) (frame r).positions
                    (ReleasedJointInterior.positions_length r (k^2)) (fun q ↦ y (E ⟨r, q⟩)))) c w -
                cellFrequency (fun c w ↦ k^2 * RecStage.mu3 r ((ReleasedJointInterior.roleEquiv r).symm i) c w) c w| ≤ δ := by
  intro δ hδ
  obtain ⟨φ, D1, D2, D3, D4, D5, D6⟩ := mme_released_level2_level3_positive_cell_correspondence
  filter_upwards [tolerance_eventually δ hδ] with k hk
  obtain ⟨hk0, hτ⟩ := hk
  have hK : 0 < k ^ 2 := by positivity
  refine ⟨fun o ↦ (mme_released_global_supported_frame o (k^2) hK).choose,
    fun r ↦ Classical.choice (mme_released_positive_integer_frame r (k^2) hK), fun E ↦ ?_⟩
  exact layout_generic (k^2) RecStage.parent3 RecStage.htotal3 RecStage.n3 RecStage.m3
    RecStage.mu3 1104 RecStage.parent2 RecStage.htotal2 RecStage.n2 RecStage.m2 RecStage.mu2
    ReleasedJointInterior.roleEquiv (fun r ↦ ReleasedJointInterior.blocks r (k^2))
    (fun r ↦ (Classical.choice (mme_released_positive_integer_frame r (k^2) hK)).positions)
    (fun r ↦ ReleasedJointInterior.positions_length r (k^2))
    (fun r ↦ (Classical.choice (mme_released_positive_integer_frame r (k^2) hK)).reference)
    (fun r ↦ (Classical.choice (mme_released_positive_integer_frame r (k^2) hK)).reference_target)
    (fun r i c ↦ (Classical.choice (mme_released_positive_integer_frame r (k^2) hK)).mass i c)
    φ D1 D2 D3 D4 D5
    (fun r i w ↦ by
      rw [parentMixture_scale _ _ _ _ _ hK, cellFrequency_scale _ hK]
      exact D6 r i w)
    _ E _ δ hτ hδ.le
