-- Prove2me | solution 1 for AlmostLossless.decode_cost
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T11:37:37.055117+00:00
-- url     : https://prove2.me/submissions/29393cca-19b4-41f9-be67-4a88c74c07c6

import Definitions.Def_Geometry_AlmostLosslessCore
import Definitions.Def_Geometry_AlmostLosslessDecoder
open AlmostLossless in
theorem solution {α : Type*} {M : ℕ} (L : List α) (H : α → Fin M) (c : Fin M) :
    (decode L H c).2 = L.length := by
  have hlen : ∀ (L : List α), (scan H c L).2 = L.length := by
    intro L
    induction L with
    | nil => rfl
    | cons a t ih => simp [scan, ih]
  exact hlen L
