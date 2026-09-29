-- Prove2me | solution 2 for AlmostLossless.blockDecode_cost
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T11:33:14.918828+00:00
-- url     : https://prove2.me/submissions/119b8a69-8f2c-4b6c-9516-b24535958a55

import Definitions.Def_Geometry_AlmostLosslessBlock
import Definitions.Def_Geometry_AlmostLosslessDecoder
open AlmostLossless in
theorem solution {β : Type*} {b M : ℕ}
    (LT : List β) (H : Fin b × β → Fin M) (c : Fin b → Fin M) :
    (blockDecode LT H c).2 = b * LT.length := by
  have hlen : ∀ (G : β → Fin M) (d : Fin M) (L : List β), (scan G d L).2 = L.length := by
    intro G d L
    induction L with
    | nil => rfl
    | cons a t ih => simp [scan, ih]
  simp only [blockDecode, decode, hlen, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
