-- Prove2me | solution 1 for UniversalPosets.minUniversalSize_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:31:15.322624+00:00
-- url     : https://prove2.me/submissions/aee3a25a-1039-4cbb-842e-f3c6a321f41c

import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_MinSize
open UniversalPosets in
theorem solution : minUniversalSize 2 = 3 := by
  classical
  have huniv : ∀ n : ℕ, IsUniversalPosetOfSize (2 ^ n) n := by
    intro n
    obtain ⟨e⟩ : Nonempty (Finset (Fin n) ≃ Fin (2 ^ n)) :=
      ⟨Fintype.equivFinOfCardEq (by simp)⟩
    refine ⟨fun a b => (e.symm a : Finset (Fin n)) ⊆ e.symm b,
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
  have hne : ∀ n : ℕ, {N | IsUniversalPosetOfSize N n}.Nonempty := fun n => ⟨2 ^ n, huniv n⟩
  have hmem : ∀ n : ℕ, IsUniversalPosetOfSize (minUniversalSize n) n := fun n =>
    Nat.sInf_mem (hne n)
  have hinj : ∀ {N n : ℕ}, IsUniversalPosetOfSize N n → n ≤ N := by
    intro N n h
    obtain ⟨H, hH, hall⟩ := h
    haveI := hH
    obtain ⟨f, hf⟩ := hall (fun x y => x = y)
      { refl := fun a => rfl
        trans := fun a b c h1 h2 => h1.trans h2
        antisymm := fun a b h1 _ => h1 }
    have hfinj : Function.Injective f := by
      intro x y hxy
      exact (hf x y).mp (by rw [hxy]; exact refl_of H (f y))
    calc n = Fintype.card (Fin n) := by simp
      _ ≤ Fintype.card (Pt N) := Fintype.card_le_of_injective f hfinj
      _ = Fintype.card (Fin N) := rfl
      _ = N := Fintype.card_fin N
  have h3 : IsUniversalPosetOfSize 3 2 := by
    refine ⟨fun a b => Fin.val a = Fin.val b ∨ (Fin.val a = 0 ∧ Fin.val b = 1), ?_, ?_⟩
    · refine { refl := fun a => Or.inl rfl
               trans := ?_
               antisymm := ?_ }
      · intro a b c hab hbc
        rcases hab with hab | ⟨ha, hb⟩
        · rcases hbc with hbc | ⟨hb', hc⟩
          · exact Or.inl (hab.trans hbc)
          · exact Or.inr ⟨hab.trans hb', hc⟩
        · rcases hbc with hbc | ⟨hb', hc⟩
          · exact Or.inr ⟨ha, hbc.symm.trans hb⟩
          · omega
      · intro a b hab hba
        rcases hab with hab | ⟨ha, hb⟩
        · exact Fin.ext hab
        · rcases hba with hba | ⟨hb', ha'⟩
          · exact Fin.ext hba.symm
          · omega
    · intro r hr
      haveI := hr
      have hr0 : r 0 0 := refl_of r 0
      have hr1 : r 1 1 := refl_of r 1
      by_cases h01 : r 0 1
      · by_cases h10 : r 1 0
        · exact absurd (antisymm_of r h01 h10) (by decide)
        · refine ⟨fun x => (if x = 0 then ⟨0, by omega⟩ else ⟨1, by omega⟩ : Fin 3), ?_⟩
          intro x y
          fin_cases x <;> fin_cases y <;> simp_all
      · by_cases h10 : r 1 0
        · refine ⟨fun x => (if x = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩ : Fin 3), ?_⟩
          intro x y
          fin_cases x <;> fin_cases y <;> simp_all
        · refine ⟨fun x => (if x = 0 then ⟨0, by omega⟩ else ⟨2, by omega⟩ : Fin 3), ?_⟩
          intro x y
          fin_cases x <;> fin_cases y <;> simp_all
  have hnot2 : ¬ IsUniversalPosetOfSize 2 2 := by
    rintro ⟨H, hH, hall⟩
    haveI := hH
    obtain ⟨f, hf⟩ := hall (fun x y => x = y)
      { refl := fun a => rfl
        trans := fun a b c h1 h2 => h1.trans h2
        antisymm := fun a b h1 _ => h1 }
    obtain ⟨g, hg⟩ := hall (fun x y => x ≤ y)
      { refl := fun a => le_refl a
        trans := fun a b c h1 h2 => h1.trans h2
        antisymm := fun a b h1 h2 => le_antisymm h1 h2 }
    have hfinj : Function.Injective f := by
      intro x y hxy
      exact (hf x y).mp (by rw [hxy]; exact refl_of H (f y))
    have hfsurj : Function.Surjective f := by
      have hcard : Fintype.card (Fin 2) = Fintype.card (Pt 2) := rfl
      exact ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcard⟩).2
    have hgne : g 0 ≠ g 1 := by
      intro h
      have h1 : (1 : Fin 2) ≤ 0 := (hg 1 0).mp (by rw [h]; exact refl_of H (g 1))
      exact absurd h1 (by decide)
    have hglt : H (g 0) (g 1) := (hg 0 1).mpr (by decide)
    obtain ⟨x, hx⟩ := hfsurj (g 0)
    obtain ⟨y, hy⟩ := hfsurj (g 1)
    have hxy : x ≠ y := by
      intro h
      rw [h, hy] at hx
      exact hgne hx.symm
    exact hxy ((hf x y).mp (by rw [hx, hy]; exact hglt))
  have hge : 3 ≤ minUniversalSize 2 := by
    have h2 := hinj (hmem 2)
    rcases Nat.lt_or_ge (minUniversalSize 2) 3 with hlt | hge
    · exfalso
      have he : minUniversalSize 2 = 2 := by omega
      have h2' := hmem 2
      rw [he] at h2'
      exact hnot2 h2'
    · exact hge
  exact le_antisymm (Nat.sInf_le h3) hge
