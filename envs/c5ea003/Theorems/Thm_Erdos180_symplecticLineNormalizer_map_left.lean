-- Prove2me | Theorems.Thm_Erdos180_symplecticLineNormalizer_map_left
-- name    : Erdos180.symplecticLineNormalizer_map_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:16:24.835863+00:00
-- url     : https://prove2.me/theorems/2c037bb7-26bb-44d0-bc87-7d3a396ec94d
-- title:
--   Normalising the first line of a disjoint pair
-- statement:
--   For disjoint lines $L, M$, the normalising automorphism carries $L$ to the standard graph
--   line with parameters $(0,0,0)$ — the "horizontal" line.
--
--   Together with the next lemma this places any disjoint line pair in a single normal form, which
--   is what reduces Proposition 4.2 to one explicit computation rather than a family of them.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L7215-L7238

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.symplecticLineNormalizer_map_left
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    symplecticAutomorphismLine K
        (symplecticLineNormalizer K L M hLM) L =
      symmetricGraphLine K 0 0 0 := by sorry
