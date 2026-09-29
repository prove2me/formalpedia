-- Prove2me | solution 1 for mme_finset_uniform_positive_fiber_truncation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:05:28.05118+00:00
-- url     : https://prove2.me/submissions/d461a1f4-d5cd-4e88-96cb-18febe502a96

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

/-- Uniformly truncate every nonempty fiber to a prescribed positive size,
without losing any fiber label. -/
theorem solution
    {α ζ : Type} [DecidableEq α] [DecidableEq ζ]
    (E : Finset α) (z : α → ζ) (H : ℕ) (hH : 0 < H)
    (hmin : ∀ c ∈ E.image z,
      H ≤ (E.filter (fun e => z e = c)).card) :
    ∃ F : Finset α,
      F ⊆ E ∧
      F.image z = E.image z ∧
      ∀ c ∈ F.image z,
        (F.filter (fun e => z e = c)).card = H := by
  classical
  let Zs : Finset ζ := E.image z
  let fiber (c : ↥Zs) : Finset α := E.filter (fun e => z e = c.1)
  have hfiberMin (c : ↥Zs) : H ≤ (fiber c).card := by
    exact hmin c.1 c.2
  let selected (c : ↥Zs) : Finset α :=
    Classical.choose (Finset.exists_subset_card_eq (hfiberMin c))
  have hselected (c : ↥Zs) :
      selected c ⊆ fiber c ∧ (selected c).card = H :=
    Classical.choose_spec (Finset.exists_subset_card_eq (hfiberMin c))
  let F : Finset α := Zs.attach.biUnion selected
  have hFE : F ⊆ E := by
    intro e he
    obtain ⟨c, _hc, hec⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_filter.mp ((hselected c).1 hec)).1
  have hImage : F.image z = E.image z := by
    apply Finset.Subset.antisymm
    · exact Finset.image_mono z hFE
    · intro c hc
      have hcZs : c ∈ Zs := hc
      let csub : ↥Zs := ⟨c, hcZs⟩
      have hselPos : 0 < (selected csub).card := by
        rw [(hselected csub).2]
        exact hH
      obtain ⟨e, heSel⟩ := Finset.card_pos.mp hselPos
      have heF : e ∈ F := by
        apply Finset.mem_biUnion.mpr
        exact ⟨csub, by simp, heSel⟩
      have hze : z e = c := by
        exact (Finset.mem_filter.mp ((hselected csub).1 heSel)).2
      exact Finset.mem_image.mpr ⟨e, heF, hze⟩
  refine ⟨F, hFE, hImage, ?_⟩
  intro c hcF
  have hcZs : c ∈ Zs := by
    rw [hImage] at hcF
    exact hcF
  let csub : ↥Zs := ⟨c, hcZs⟩
  have hfiberEq :
      F.filter (fun e => z e = c) = selected csub := by
    ext e
    constructor
    · intro he
      have heF := (Finset.mem_filter.mp he).1
      have hze := (Finset.mem_filter.mp he).2
      obtain ⟨d, _hd, hed⟩ := Finset.mem_biUnion.mp heF
      have hzed : z e = d.1 :=
        (Finset.mem_filter.mp ((hselected d).1 hed)).2
      have hdc : d = csub := by
        apply Subtype.ext
        exact hzed.symm.trans hze
      simpa [hdc] using hed
    · intro he
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_biUnion.mpr
        exact ⟨csub, by simp, he⟩
      · exact (Finset.mem_filter.mp ((hselected csub).1 he)).2
  rw [hfiberEq, (hselected csub).2]
