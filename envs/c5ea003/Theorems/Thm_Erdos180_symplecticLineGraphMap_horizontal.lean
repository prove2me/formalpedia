-- Prove2me | Theorems.Thm_Erdos180_symplecticLineGraphMap_horizontal
-- name    : Erdos180.symplecticLineGraphMap_horizontal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:17:02.801168+00:00
-- url     : https://prove2.me/theorems/e65264c3-de62-474b-bb12-6427b640cca0
-- title:
--   The graph map of a line in normalised coordinates
-- statement:
--   For a line $L$ disjoint from the vertical line, the associated graph map sends the
--   horizontal projection of a vector of $L$ to its vertical projection.
--
--   This exhibits every line disjoint from the vertical one as the graph of a linear map from the
--   horizontal to the vertical coordinate plane — the parametrisation in which lines acquire the
--   parameters $(a,b,c)$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L7364-L7378

import Definitions.Def_erdos180_core4
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.symplecticLineGraphMap_horizontal
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1)
    (x : L.1) :
    symplecticLineGraphMap K L hvertical
        (symplecticHorizontalProjection K
          (x : SymplecticVector K)) =
      symplecticVerticalProjection K
        (x : SymplecticVector K) := by sorry
