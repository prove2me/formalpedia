-- Prove2me | Theorems.Thm_Erdos180_symplecticLine_eq_invertible_symmetricGraphLine
-- name    : Erdos180.symplecticLine_eq_invertible_symmetricGraphLine
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:17:21.360111+00:00
-- url     : https://prove2.me/theorems/4accbf13-a51e-4887-9430-aa34a07e8faa
-- title:
--   Lines disjoint from both coordinate lines are invertible graphs
-- statement:
--   A line disjoint from the vertical line and from the horizontal line equals a graph line
--   with parameters $(a,b,c)$ whose determinant $ac - b^2$ is nonzero.
--
--   Isotropy forces the graph map to be *symmetric*, and disjointness from the horizontal line forces
--   it to be invertible. This classification of lines is the coordinate backbone of §4.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L7616-L7630

import Definitions.Def_erdos180_core4
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.symplecticLine_eq_invertible_symmetricGraphLine
    (L : SymplecticLine K)
    (hvertical : Disjoint L.1 (symplecticVerticalLine K).1)
    (hhorizontal :
      Disjoint L.1 (symmetricGraphLine K 0 0 0).1) :
    ∃ a b c : K,
      L = symmetricGraphLine K a b c ∧
        symmetricDet a b c ≠ 0 := by sorry
