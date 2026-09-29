-- Prove2me | solution 1 for UniversalPosets.three_poset_bound_of_isUniversalPosetOfSize
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T16:56:22.454098+00:00
-- url     : https://prove2.me/submissions/f271fbac-661d-4efc-b0c3-873cb2785f15

import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_ExactSmall
import Definitions.Def_Cryptography_UniversalPosets_MinSize
import Definitions.Def_Cryptography_UniversalPosets_ThreePosetBound
open UniversalPosets in
theorem solution {N n : ℕ} (h : IsUniversalPosetOfSize N n) : 3 * n - (3 + (n + 1) / 2) ≤ N := by
  classical
  obtain ⟨H, hH, huniv⟩ := h
  haveI := hH
  -- an induced embedding of a partial order is injective
  have hinj : ∀ (q : Fin n → Fin n → Prop), IsPartialOrder (Fin n) q → ∀ e : Fin n → Pt N,
      (∀ x y, H (e x) (e y) ↔ q x y) → Function.Injective e := by
    intro q hq e he x y hxy
    haveI := hq
    have h1 : q x y := (he x y).mp (by rw [hxy]; exact refl_of H _)
    have h2 : q y x := (he y x).mp (by rw [hxy]; exact refl_of H _)
    exact antisymm_of q h1 h2
  -- two induced copies overlap in at most a common-induced-subposet bound
  have hov : ∀ (q q' : Fin n → Fin n → Prop) (s : ℕ) (e e' : Fin n → Pt N),
      Function.Injective e → (∀ x y, H (e x) (e y) ↔ q x y) → (∀ x y, H (e' x) (e' y) ↔ q' x y) →
      CommonInducedBound q q' s → (Finset.univ.image e ∩ Finset.univ.image e').card ≤ s := by
    intro q q' s e e' hei he he' hs
    let A : Finset (Fin n) := Finset.univ.filter fun x => ∃ y, e' y = e x
    let φ : Fin n → Fin n := fun x => if hx : ∃ y, e' y = e x then hx.choose else x
    have hφ : ∀ x ∈ A, e' (φ x) = e x := by
      intro x hx
      have hx' : ∃ y, e' y = e x := (Finset.mem_filter.mp hx).2
      simp only [φ, dif_pos hx']
      exact hx'.choose_spec
    have hA : A.card ≤ s := by
      apply hs A φ
      · intro x hx y hy hxy
        apply hei
        rw [← hφ x hx, ← hφ y hy, hxy]
      · intro x hx y hy
        rw [← he x y, ← he' (φ x) (φ y), hφ x hx, hφ y hy]
    calc (Finset.univ.image e ∩ Finset.univ.image e').card ≤ (A.image e).card := by
          apply Finset.card_le_card
          intro z hz
          rw [Finset.mem_inter, Finset.mem_image, Finset.mem_image] at hz
          obtain ⟨⟨x, -, rfl⟩, ⟨y, -, hy⟩⟩ := hz
          exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, y, hy⟩, rfl⟩
      _ ≤ A.card := Finset.card_image_le
      _ ≤ s := hA
  -- the three posets: chain, antichain, two chains
  set hh := (n + 1) / 2 with hhdef
  have hchain : IsPartialOrder (Fin n) (· ≤ ·) := inferInstance
  have hanti : IsPartialOrder (Fin n) (· = ·) :=
    { refl := fun a => rfl, trans := fun a b c h1 h2 => h1.trans h2,
      antisymm := fun a b h _ => h }
  have htwo : IsPartialOrder (Fin n) (twoChains n) :=
    { refl := fun a => ⟨le_rfl, Iff.rfl⟩,
      trans := fun a b c h1 h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩,
      antisymm := fun a b h1 h2 => le_antisymm h1.1 h2.1 }
  -- chain vs antichain: at most one common point
  have b1 : CommonInducedBound (· ≤ · : Fin n → Fin n → Prop) (· = ·) 1 := by
    intro A φ hφ hiff
    refine Finset.card_le_one.mpr fun x hx y hy => ?_
    rcases le_total x y with hxy | hxy
    · exact hφ hx hy ((hiff x hx y hy).mp hxy)
    · exact (hφ hy hx ((hiff y hy x hx).mp hxy)).symm
  -- chain vs two chains: a common subposet sits in one of the two chains
  have b2 : CommonInducedBound (· ≤ · : Fin n → Fin n → Prop) (twoChains n) hh := by
    intro A φ hφ hiff
    rcases A.eq_empty_or_nonempty with hA | ⟨x₀, hx₀⟩
    · rw [hA]; simp
    have hside : ∀ x ∈ A, ((φ x : ℕ) < hh ↔ (φ x₀ : ℕ) < hh) := by
      intro x hx
      rcases le_total x x₀ with h1 | h1
      · exact ((hiff x hx x₀ hx₀).mp h1).2
      · exact ((hiff x₀ hx₀ x hx).mp h1).2.symm
    rw [← Finset.card_image_of_injOn hφ]
    by_cases hlow : (φ x₀ : ℕ) < hh
    · calc (A.image φ).card ≤ (Finset.range hh).card := by
            apply Finset.card_le_card_of_injOn (fun z : Fin n => (z : ℕ))
            · intro z hz
              obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
              exact Finset.mem_coe.mpr (Finset.mem_range.mpr ((hside x hx).mpr hlow))
            · intro a _ b _ hab
              exact Fin.ext hab
        _ = hh := Finset.card_range hh
    · calc (A.image φ).card ≤ (Finset.range (n - hh)).card := by
            apply Finset.card_le_card_of_injOn (fun z : Fin n => (z : ℕ) - hh)
            · intro z hz
              obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
              have h1 := (hside x hx).not.mpr hlow
              have h2 := (φ x).isLt
              refine Finset.mem_coe.mpr (Finset.mem_range.mpr ?_)
              show ((φ x : Fin n) : ℕ) - hh < n - hh
              omega
            · intro a ha b hb hab
              obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
              obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
              have h1 := (hside x hx).not.mpr hlow
              have h2 := (hside y hy).not.mpr hlow
              simp only at hab
              exact Fin.ext (by omega)
        _ ≤ hh := by rw [Finset.card_range]; omega
  -- antichain vs two chains: distinct common points lie in different chains
  have b3 : CommonInducedBound (· = · : Fin n → Fin n → Prop) (twoChains n) 2 := by
    intro A φ hφ hiff
    calc A.card ≤ (Finset.univ : Finset Bool).card := by
          apply Finset.card_le_card_of_injOn (fun x => decide ((φ x : ℕ) < hh))
          · intro x _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
          · intro x hx y hy hxy
            simp only [decide_eq_decide] at hxy
            by_contra hne
            rcases le_total (φ x) (φ y) with h1 | h1
            · exact hne ((hiff x hx y hy).mpr ⟨h1, hxy⟩)
            · exact hne ((hiff y hy x hx).mpr ⟨h1, hxy.symm⟩).symm
      _ = 2 := rfl
  -- embed the three posets
  obtain ⟨f, hf⟩ := huniv _ hchain
  obtain ⟨g, hg⟩ := huniv _ hanti
  obtain ⟨k, hk⟩ := huniv _ htwo
  have hfi := hinj _ hchain f hf
  have hgi := hinj _ hanti g hg
  have hki := hinj _ htwo k hk
  have o1 := hov _ _ _ f g hfi hf hg b1
  have o2 := hov _ _ _ f k hfi hf hk b2
  have o3 := hov _ _ _ g k hgi hg hk b3
  -- Bonferroni for three sets inside the `N` points
  set F := Finset.univ.image f
  set G := Finset.univ.image g
  set K := Finset.univ.image k
  have cF : F.card = n := by rw [Finset.card_image_of_injective _ hfi, Finset.card_univ, Fintype.card_fin]
  have cG : G.card = n := by rw [Finset.card_image_of_injective _ hgi, Finset.card_univ, Fintype.card_fin]
  have cK : K.card = n := by rw [Finset.card_image_of_injective _ hki, Finset.card_univ, Fintype.card_fin]
  have u1 := Finset.card_union_add_card_inter F G
  have u2 := Finset.card_union_add_card_inter (F ∪ G) K
  have u3 : ((F ∪ G) ∩ K).card ≤ (F ∩ K).card + (G ∩ K).card := by
    rw [Finset.union_inter_distrib_right]
    exact Finset.card_union_le _ _
  have hle : (F ∪ G ∪ K).card ≤ N := by
    calc (F ∪ G ∪ K).card ≤ (Finset.univ : Finset (Pt N)).card := Finset.card_le_univ _
      _ = N := Fintype.card_fin N
  omega
