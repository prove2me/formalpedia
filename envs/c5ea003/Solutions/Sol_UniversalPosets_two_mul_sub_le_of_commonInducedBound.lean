-- Prove2me | solution 1 for UniversalPosets.two_mul_sub_le_of_commonInducedBound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T16:51:20.604575+00:00
-- url     : https://prove2.me/submissions/d7c39d43-1244-4600-883f-bdd5ed798416

import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_ExactSmall
import Definitions.Def_Cryptography_UniversalPosets_MinSize
open UniversalPosets in
theorem solution {N n s : ℕ} (h : IsUniversalPosetOfSize N n)
    {r r' : Fin n → Fin n → Prop} (hr : IsPartialOrder (Fin n) r)
    (hr' : IsPartialOrder (Fin n) r') (hs : CommonInducedBound r r' s) :
    2 * n - s ≤ N := by
  classical
  obtain ⟨H, hH, huniv⟩ := h
  haveI := hH
  obtain ⟨f, hf⟩ := huniv r hr
  obtain ⟨g, hg⟩ := huniv r' hr'
  -- an induced embedding of a partial order is injective
  have hinj : ∀ (q : Fin n → Fin n → Prop), IsPartialOrder (Fin n) q → ∀ e : Fin n → Pt N,
      (∀ x y, H (e x) (e y) ↔ q x y) → Function.Injective e := by
    intro q hq e he x y hxy
    haveI := hq
    have h1 : q x y := (he x y).mp (by rw [hxy]; exact refl_of H _)
    have h2 : q y x := (he y x).mp (by rw [hxy]; exact refl_of H _)
    exact antisymm_of q h1 h2
  have hfi := hinj r hr f hf
  have hgi := hinj r' hr' g hg
  -- the points of `r` whose image is also hit by `g`, and the induced matching `φ`
  let A : Finset (Fin n) := Finset.univ.filter fun x => ∃ y, g y = f x
  let φ : Fin n → Fin n := fun x => if hx : ∃ y, g y = f x then hx.choose else x
  have hφ : ∀ x ∈ A, g (φ x) = f x := by
    intro x hx
    have hx' : ∃ y, g y = f x := (Finset.mem_filter.mp hx).2
    simp only [φ, dif_pos hx']
    exact hx'.choose_spec
  -- `φ` is a common induced subposet, so `|A| ≤ s`
  have hA : A.card ≤ s := by
    apply hs A φ
    · intro x hx y hy hxy
      apply hfi
      rw [← hφ x hx, ← hφ y hy, hxy]
    · intro x hx y hy
      rw [← hf x y, ← hg (φ x) (φ y), hφ x hx, hφ y hy]
  -- the two images overlap in at most `|A|` points
  have hinter : (Finset.univ.image f ∩ Finset.univ.image g).card ≤ A.card := by
    calc (Finset.univ.image f ∩ Finset.univ.image g).card ≤ (A.image f).card := by
          apply Finset.card_le_card
          intro z hz
          rw [Finset.mem_inter, Finset.mem_image, Finset.mem_image] at hz
          obtain ⟨⟨x, -, rfl⟩, ⟨y, -, hy⟩⟩ := hz
          exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, y, hy⟩, rfl⟩
      _ ≤ A.card := Finset.card_image_le
  -- inclusion–exclusion inside the `N` points
  have hunion := Finset.card_union_add_card_inter (Finset.univ.image f) (Finset.univ.image g)
  rw [Finset.card_image_of_injective _ hfi, Finset.card_image_of_injective _ hgi,
    Finset.card_univ, Fintype.card_fin] at hunion
  have hle : (Finset.univ.image f ∪ Finset.univ.image g).card ≤ N := by
    calc (Finset.univ.image f ∪ Finset.univ.image g).card ≤ (Finset.univ : Finset (Pt N)).card :=
          Finset.card_le_univ _
      _ = N := Fintype.card_fin N
  omega
