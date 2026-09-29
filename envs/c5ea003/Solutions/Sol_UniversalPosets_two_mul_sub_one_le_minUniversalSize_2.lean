-- Prove2me | solution 2 for UniversalPosets.two_mul_sub_one_le_minUniversalSize
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:28:10.146198+00:00
-- url     : https://prove2.me/submissions/8af72917-6da2-4724-89fa-9c54e8544ade

import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_MinSize
open UniversalPosets in
theorem solution (n : ℕ) : 2 * n - 1 ≤ minUniversalSize n := by
  classical
  -- ===== the set of universal sizes is nonempty: the Boolean lattice works =====
  have huniv : ∀ m : ℕ, IsUniversalPosetOfSize (2 ^ m) m := by
    intro m
    obtain ⟨e⟩ : Nonempty (Finset (Fin m) ≃ Fin (2 ^ m)) :=
      ⟨Fintype.equivFinOfCardEq (by simp)⟩
    refine ⟨fun a b => (e.symm a : Finset (Fin m)) ⊆ e.symm b,
      { refl := fun a => Finset.Subset.refl _
        trans := fun a b c hab hbc => hab.trans hbc
        antisymm := fun a b hab hba => e.symm.injective (Finset.Subset.antisymm hab hba) }, ?_⟩
    intro r hr
    haveI := hr
    refine ⟨fun x => e (Finset.univ.filter (fun y => r y x)), ?_⟩
    intro x y
    simp only [Equiv.symm_apply_apply]
    constructor
    · intro hsub
      have hx : x ∈ Finset.univ.filter (fun y => r y x) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact refl_of r x
      have hmem := hsub hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      exact hmem
    · intro hxy z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact trans_of r hz hxy
  have hne : {N | IsUniversalPosetOfSize N n}.Nonempty := ⟨2 ^ n, huniv n⟩
  obtain ⟨H, hH, hall⟩ : IsUniversalPosetOfSize (minUniversalSize n) n := Nat.sInf_mem hne
  -- ===== a chain of n points and an antichain of n points both embed =====
  haveI hchain : IsPartialOrder (Fin n) (fun x y => x ≤ y) :=
    { refl := fun a => le_refl a
      trans := fun a b c hab hbc => le_trans hab hbc
      antisymm := fun a b hab hba => le_antisymm hab hba }
  haveI hanti : IsPartialOrder (Fin n) (fun x y => x = y) :=
    { refl := fun _ => rfl
      trans := fun a b c hab hbc => hab.trans hbc
      antisymm := fun a b hab _ => hab }
  obtain ⟨f, hf⟩ := hall (fun x y => x ≤ y) hchain
  obtain ⟨g, hg⟩ := hall (fun x y => x = y) hanti
  have hfinj : Function.Injective f := by
    intro x y hxy
    have h1 : H (f x) (f y) := by rw [hxy]; exact (hf y y).mpr (le_refl y)
    have h2 : H (f y) (f x) := by rw [hxy]; exact (hf y y).mpr (le_refl y)
    exact le_antisymm ((hf x y).mp h1) ((hf y x).mp h2)
  have hginj : Function.Injective g := by
    intro x y hxy
    have h1 : H (g x) (g y) := by rw [hxy]; exact (hg y y).mpr rfl
    exact (hg x y).mp h1
  -- ===== the two images meet in at most one point =====
  set S := Finset.univ.image f with hS
  set T := Finset.univ.image g with hT
  have hScard : S.card = n := by
    rw [hS, Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
  have hTcard : T.card = n := by
    rw [hT, Finset.card_image_of_injective _ hginj, Finset.card_univ, Fintype.card_fin]
  have hinter : (S ∩ T).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p hp q hq
    simp only [hS, hT, Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and] at hp hq
    obtain ⟨⟨a, hafp⟩, ⟨b, hbgp⟩⟩ := hp
    obtain ⟨⟨c, hcfq⟩, ⟨d, hdgq⟩⟩ := hq
    -- `p = f a = g b` and `q = f c = g d`
    have e1 : g b = f a := hbgp.trans hafp.symm
    have e2 : g d = f c := hdgq.trans hcfq.symm
    -- two points of the chain image are comparable, two of the antichain image are not
    have hbd : b = d := by
      rcases le_total a c with hac | hac
      · have : H (g b) (g d) := by rw [e1, e2]; exact (hf a c).mpr hac
        exact (hg b d).mp this
      · have : H (g d) (g b) := by rw [e1, e2]; exact (hf c a).mpr hac
        exact ((hg d b).mp this).symm
    rw [← hbgp, ← hdgq, hbd]
  -- ===== so the host has at least `n + n - 1` points =====
  have hunion : (S ∪ T).card ≤ minUniversalSize n := by
    calc (S ∪ T).card ≤ (Finset.univ : Finset (Pt (minUniversalSize n))).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = minUniversalSize n := by
          rw [Finset.card_univ]
          exact Fintype.card_fin _
  have hadd : (S ∪ T).card + (S ∩ T).card = S.card + T.card :=
    Finset.card_union_add_card_inter S T
  omega
