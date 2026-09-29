-- Prove2me | solution 1 for UniversalPosets.isUniversalPosetOfSize_pred
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T16:46:34.314317+00:00
-- url     : https://prove2.me/submissions/c54a6c09-b5ef-4158-80e4-2652f1fb69c6

import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_MinSize
import Definitions.Def_Cryptography_UniversalPosets_StrictMono
open UniversalPosets in
theorem solution {N n : ℕ} (h : IsUniversalPosetOfSize N (n + 1)) :
    IsUniversalPosetOfSize (N - 1) n := by
  classical
  obtain ⟨H, hH, huniv⟩ := h
  haveI := hH
  -- the discrete order on `n + 1` points embeds, so the carrier is nonempty
  have hpos : 0 < N := by
    have hdisc : IsPartialOrder (Fin (n + 1)) (· = ·) :=
      { refl := fun a => rfl, trans := fun a b c h1 h2 => h1.trans h2,
        antisymm := fun a b h _ => h }
    obtain ⟨f, -⟩ := huniv _ hdisc
    exact Fin.pos (show Fin N from f 0)
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  show IsUniversalPosetOfSize N' n
  -- a maximal point `m`: maximise the size of the down-set
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image (Finset.univ : Finset (Pt (N' + 1)))
    (fun x => (Finset.univ.filter fun y => H y x).card)
    ⟨show Pt (N' + 1) from (0 : Fin (N' + 1)), Finset.mem_univ _⟩
  have hmax : ∀ y, H m y → y = m := by
    intro y hmy
    by_contra hne
    have hsub : (Finset.univ.filter fun z => H z m) ⊂ (Finset.univ.filter fun z => H z y) := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨y, by simp [refl_of H y], ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro hym
        exact hne (antisymm_of H hym hmy)
      · intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        exact trans_of H hz hmy
    have h1 := hm y (Finset.mem_univ y)
    have h2 := Finset.card_lt_card hsub
    omega
  -- the order induced on the other `N'` points, via `succAbove m`
  refine ⟨fun a b => H (Fin.succAbove (m : Fin (N' + 1)) a) (Fin.succAbove (m : Fin (N' + 1)) b),
    ?_, ?_⟩
  · exact { refl := fun a => refl_of H _, trans := fun a b c h1 h2 => trans_of H h1 h2,
            antisymm := fun a b h1 h2 => Fin.succAbove_right_injective (antisymm_of H h1 h2) }
  · intro r hr
    haveI := hr
    -- adjoin a new top element to `r`
    let r' : Fin (n + 1) → Fin (n + 1) → Prop := fun x y =>
      y = Fin.last n ∨ ∃ a b, x = Fin.castSucc a ∧ y = Fin.castSucc b ∧ r a b
    have hr' : IsPartialOrder (Fin (n + 1)) r' :=
      { refl := fun x => by
          rcases Fin.eq_castSucc_or_eq_last x with ⟨a, rfl⟩ | rfl
          · exact Or.inr ⟨a, a, rfl, rfl, refl_of r a⟩
          · exact Or.inl rfl
        trans := fun x y z h1 h2 => by
          rcases h2 with hz | ⟨b, c, hy, hz, hbc⟩
          · exact Or.inl hz
          rcases h1 with hy' | ⟨a, b', hx, hy', hab⟩
          · rw [hy] at hy'
            exact absurd hy' (Fin.castSucc_lt_last b).ne
          · rw [hy] at hy'
            obtain rfl := Fin.castSucc_inj.mp hy'
            exact Or.inr ⟨a, c, hx, hz, trans_of r hab hbc⟩
        antisymm := fun x y h1 h2 => by
          rcases h1 with hy | ⟨a, b, hx, hy, hab⟩ <;> rcases h2 with hx' | ⟨b', a', hy', hx', hba⟩
          · rw [hy, hx']
          · rw [hy] at hy'
            exact absurd hy'.symm (Fin.castSucc_lt_last b').ne
          · rw [hx] at hx'
            exact absurd hx' (Fin.castSucc_lt_last a).ne
          · rw [hx] at hx'
            rw [hy] at hy'
            obtain rfl := Fin.castSucc_inj.mp hx'
            obtain rfl := Fin.castSucc_inj.mp hy'
            rw [hx, hy, antisymm_of r hab hba] }
    obtain ⟨f', hf'⟩ := huniv r' hr'
    -- old points land away from the maximal point `m` (they lie strictly below the new top)
    have havoid : ∀ a : Fin n, (f' (Fin.castSucc a) : Fin (N' + 1)) ≠ m := by
      intro a ha
      have h1 : H (f' (Fin.castSucc a)) (f' (Fin.last n)) := (hf' _ _).mpr (Or.inl rfl)
      have h2 : f' (Fin.last n) = m := hmax _ (ha ▸ h1)
      have h3 : H (f' (Fin.last n)) (f' (Fin.castSucc a)) := by
        rw [h2]
        exact ha ▸ refl_of H _
      rcases (hf' _ _).mp h3 with h | ⟨a', b', hl, _, _⟩
      · exact (Fin.castSucc_lt_last a).ne h
      · exact (Fin.castSucc_lt_last a').ne' hl
    choose f hf using fun a => Fin.exists_succAbove_eq (havoid a)
    refine ⟨f, fun a b => ?_⟩
    show H (Fin.succAbove (m : Fin (N' + 1)) (f a)) (Fin.succAbove (m : Fin (N' + 1)) (f b)) ↔ r a b
    rw [hf a, hf b, hf']
    constructor
    · rintro (h | ⟨a', b', ha', hb', hab⟩)
      · exact absurd h (Fin.castSucc_lt_last b).ne
      · rw [Fin.castSucc_inj.mp ha', Fin.castSucc_inj.mp hb']
        exact hab
    · intro hab
      exact Or.inr ⟨a, b, rfl, rfl, hab⟩
