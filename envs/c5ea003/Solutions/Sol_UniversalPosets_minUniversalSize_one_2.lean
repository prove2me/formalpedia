-- Prove2me | solution 2 for UniversalPosets.minUniversalSize_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-17T19:36:54.007189+00:00
-- url     : https://prove2.me/submissions/fb4c706c-eb2d-4749-996a-d94cdc546b45

import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_ExactSmall
import Definitions.Def_Cryptography_UniversalPosets_MinSize

open UniversalPosets Function

private instance eq_isPartialOrder {α : Type*} : IsPartialOrder α (· = ·) where
  refl := fun _ => rfl
  trans := fun _ _ _ => Eq.trans
  antisymm := fun _ _ h _ => h

private lemma univ_one : IsUniversalPosetOfSize 1 1 := by
  refine ⟨(· = ·), inferInstance, ?_⟩
  intro r hr
  refine ⟨fun _ => (⟨0, by decide⟩ : Pt 1), ?_⟩
  intro x y
  have hx : x = (0 : Fin 1) := Subsingleton.elim _ _
  have hy : y = (0 : Fin 1) := Subsingleton.elim _ _
  subst hx; subst hy
  constructor
  · intro; exact hr.refl (0 : Fin 1)
  · intro; rfl

theorem solution : minUniversalSize 1 = 1 := by
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _) univ_one
  · refine le_csInf ⟨1, univ_one⟩ ?_
    intro N hN
    obtain ⟨H, _, huniv⟩ := hN
    obtain ⟨f, _⟩ := huniv (fun a b => a = b) inferInstance
    exact Fin.pos_iff_nonempty.mpr ⟨f 0⟩
