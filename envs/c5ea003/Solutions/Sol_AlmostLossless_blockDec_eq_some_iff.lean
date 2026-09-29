-- Prove2me | solution 1 for AlmostLossless.blockDec_eq_some_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T11:51:57.827036+00:00
-- url     : https://prove2.me/submissions/668221b9-d5db-4dd2-b04e-49fd34b6d3ef

import Definitions.Def_Bridges_AlmostLosslessBlockDecoding
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
open AlmostLossless in
theorem solution {β : Type*} {b m : ℕ} {l : Fin b → List β} {h : Fin b → β → Fin m}
    {c : Fin b → Fin m} {x : Fin b → β} :
    blockDec l h c = some x ↔ ∀ j, decodeList (h j) (l j) (c j) = some (x j) := by
  unfold blockDec
  constructor
  · intro H j
    split_ifs at H with hall
    have hx := Option.some.inj H
    subst hx
    exact (Option.some_get _).symm
  · intro H
    have hall : ∀ j, (decodeList (h j) (l j) (c j)).isSome := fun j => by rw [H j]; rfl
    rw [dif_pos hall]
    congr 1
    funext j
    exact (Option.eq_some_iff_get_eq.mp (H j)).choose_spec
