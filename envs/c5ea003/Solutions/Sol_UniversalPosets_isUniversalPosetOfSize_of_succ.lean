-- Prove2me | solution 1 for UniversalPosets.isUniversalPosetOfSize_of_succ
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:20:39.542868+00:00
-- url     : https://prove2.me/submissions/62ad482c-9d4f-40c7-a43e-d39f99ec07fc

import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_ExactSmall
import Definitions.Def_Cryptography_UniversalPosets_MinSize
open UniversalPosets Function in
theorem solution {N n : ℕ} (h : IsUniversalPosetOfSize N (n + 1)) :
    IsUniversalPosetOfSize N n := by
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
  have hsucc : ∀ {N n : ℕ}, IsUniversalPosetOfSize N (n + 1) → IsUniversalPosetOfSize N n := by
    intro N n h
    obtain ⟨H, hH, hall⟩ := h
    refine ⟨H, hH, ?_⟩
    intro r hr
    haveI := hr
    set r' : Fin (n + 1) → Fin (n + 1) → Prop :=
      fun x y => (x : ℕ) = (y : ℕ) ∨ ∃ hx : (x : ℕ) < n, ∃ hy : (y : ℕ) < n, r ⟨x, hx⟩ ⟨y, hy⟩
      with hr'
    have hr'po : IsPartialOrder (Fin (n + 1)) r' := by
      refine { refl := fun a => ?_, trans := fun a b c hab hbc => ?_, antisymm := fun a b hab hba => ?_ }
      · exact Or.inl rfl
      · rcases hab with hab | ⟨ha, hb, hab⟩
        · have : a = b := Fin.ext hab
          subst this
          exact hbc
        · rcases hbc with hbc | ⟨hb', hc, hbc⟩
          · have : b = c := Fin.ext hbc
            subst this
            exact Or.inr ⟨ha, hb, hab⟩
          · exact Or.inr ⟨ha, hc, trans_of r hab hbc⟩
      · rcases hab with hab | ⟨ha, hb, hab⟩
        · exact Fin.ext hab
        · rcases hba with hba | ⟨hb', ha', hba⟩
          · exact (Fin.ext hba).symm
          · have := antisymm_of r hab hba
            exact Fin.ext (by simpa using congrArg Fin.val this)
    obtain ⟨f, hf⟩ := hall r' hr'po
    refine ⟨fun x => f ⟨(x : ℕ), by omega⟩, ?_⟩
    intro x y
    rw [hf]
    simp only [hr']
    constructor
    · rintro (hxy | ⟨hx, hy, hxy⟩)
      · have : x = y := Fin.ext (by simpa using hxy)
        subst this
        exact refl_of r x
      · exact hxy
    · intro hxy
      exact Or.inr ⟨x.isLt, y.isLt, hxy⟩
  exact hsucc h
