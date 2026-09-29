-- Prove2me | solution 1 for UniversalPosets.isUniversalPosetOfSize_minUniversalSize
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T07:24:19.360927+00:00
-- url     : https://prove2.me/submissions/643341c6-e34c-48bd-8cdf-969f42a7fda6

import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_MinSize
open UniversalPosets in
theorem solution (n : ℕ) : IsUniversalPosetOfSize (minUniversalSize n) n := by
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
  exact hmem n
