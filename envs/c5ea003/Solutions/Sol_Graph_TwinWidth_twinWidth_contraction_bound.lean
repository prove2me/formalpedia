-- Prove2me | solution 1 for Graph.TwinWidth.twinWidth_contraction_bound
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T20:21:19.563053+00:00
-- url     : https://prove2.me/submissions/8ddfd86e-7b34-4864-a56c-508a49b52356

import Mathlib
import Definitions.Def_Geometry_Contractions

open Graph.TwinWidth

variable {V : Type*}

theorem solution (l : List V) :
    (starSequence l).length ≤ 2 * l.length := by
  cases l with
  | nil => simp [starSequence]
  | cons v₀ rest =>
      simp [starSequence, List.length_map]
      omega
