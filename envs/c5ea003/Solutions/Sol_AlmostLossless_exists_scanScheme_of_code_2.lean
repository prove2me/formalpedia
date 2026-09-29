-- Prove2me | solution 2 for AlmostLossless.exists_scanScheme_of_code
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T13:00:06.493159+00:00
-- url     : https://prove2.me/submissions/aef43144-1e55-4526-915c-29522dae31f1

import Definitions.Def_Logic_AlmostLossless_Core
import Definitions.Def_Logic_AlmostLossless_Instances
import Definitions.Def_Logic_AlmostLossless_Scheme
open AlmostLossless in
theorem solution {S : Type*} {C : Type*} [Fintype S] [DecidableEq S] [DecidableEq C]
    (K : Code S C) :
    ∃ P : ScanScheme S Unit C,
      (∀ s : S, Correct (P.code ()) s ↔ Correct K s) ∧
      Honest (P.code ()) ∧
      (∀ m : C, P.decodeCost () m ≤ 1) := by
  let T : Finset S := Finset.univ.filter (fun s => Correct K s)
  let P : ScanScheme S Unit C :=
    { typical := T
      hash := fun _ s => K.enc s
      cand := fun _ m => T.filter (fun s => K.dec m = some s)
      cand_subset := fun _ _ => Finset.filter_subset _ _
      self_mem_cand := fun _ s hs => Finset.mem_filter.mpr ⟨hs, (Finset.mem_filter.mp hs).2⟩ }
  have hcand : ∀ s ∈ T, P.cand () (K.enc s) = {s} := by
    intro s hs
    have hcs : K.dec (K.enc s) = some s := (Finset.mem_filter.mp hs).2
    ext t
    simp only [P, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, ht⟩
      rw [hcs] at ht
      exact (Option.some.inj ht).symm
    · rintro rfl
      exact ⟨hs, hcs⟩
  have hdecT : ∀ s ∈ T, (P.code ()).dec ((P.code ()).enc s) = some s := by
    intro s hs
    have henc : (P.code ()).enc s = some (K.enc s) := by
      simp only [ScanScheme.code, P, if_pos hs]
    rw [henc]
    show P.decode () (K.enc s) = some s
    unfold ScanScheme.decode
    rw [hcand s hs]
    simp [scan, scanStep, P]
  have hdecN : ∀ s ∉ T, (P.code ()).dec ((P.code ()).enc s) = none := by
    intro s hs
    have henc : (P.code ()).enc s = none := by
      simp only [ScanScheme.code, P, if_neg hs]
    rw [henc]
    rfl
  refine ⟨P, ?_, ?_, ?_⟩
  · intro s
    by_cases hs : s ∈ T
    · have hK : Correct K s := (Finset.mem_filter.mp hs).2
      exact ⟨fun _ => hK, fun _ => hdecT s hs⟩
    · have hK : ¬ Correct K s := fun h => hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      constructor
      · intro h
        exfalso
        have h' : (P.code ()).dec ((P.code ()).enc s) = some s := h
        rw [hdecN s hs] at h'
        simp at h'
      · intro h
        exact absurd h hK
  · intro s
    by_cases hs : s ∈ T
    · exact Or.inl (hdecT s hs)
    · exact Or.inr (hdecN s hs)
  · intro m
    unfold ScanScheme.decodeCost
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [P, Finset.mem_filter] at ha hb
    rw [ha.2] at hb
    exact Option.some.inj hb.2
