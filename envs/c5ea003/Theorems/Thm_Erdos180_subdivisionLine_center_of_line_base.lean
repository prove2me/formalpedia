-- Prove2me | Theorems.Thm_Erdos180_subdivisionLine_center_of_line_base
-- name    : Erdos180.subdivisionLine_center_of_line_base
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:07:31.830533+00:00
-- url     : https://prove2.me/theorems/c5ad5905-7a23-4ca1-9f65-7b97806617c6
-- title:
--   A copy of $S_k$ based at lines has its centres at lines
-- statement:
--   The dual of the corresponding statement for points: if a copy of $S_k$ sends some base to
--   a line, it sends every centre to a line.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L2498-L2523

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.subdivisionLine_center_of_line_base
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {L : SymplecticLine K}
    (hbase : copy (.inl (.inl base)) = .inr L) :
    ∃ C : SymplecticLine K,
      copy (.inl (.inr center)) = .inr C := by sorry
