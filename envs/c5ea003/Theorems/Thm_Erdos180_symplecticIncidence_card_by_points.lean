-- Prove2me | Theorems.Thm_Erdos180_symplecticIncidence_card_by_points
-- name    : Erdos180.symplecticIncidence_card_by_points
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:04:05.282106+00:00
-- url     : https://prove2.me/theorems/f01d8ffd-d6d7-4f46-aabf-52a4f0d27d83
-- title:
--   The number of incidences of $W(q)$
-- statement:
--   The number of point-line incidences of the quadrangle is
--
--   $$|\mathcal{I}| \;=\; |\mathcal{P}| \cdot (q+1),$$
--
--   since every point lies on exactly $q+1$ lines.
--
--   Combined with the point count this gives $e_q = (q+1)^2(q^2+1) \ge 2^{-4/3} n_q^{4/3}$,
--   equation (8) of the source — the edge density that makes $I_q$ a witness for
--   $\mathrm{ex}(n,F) = \Omega(n^{4/3})$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L1403-L1420

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.SetLike.Fintype
import Mathlib.LinearAlgebra.Dimension.Finrank

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.symplecticIncidence_card_by_points [Finite K] :
    Nat.card (SymplecticIncidence K) =
      Nat.card (SymplecticPoint K) * (Nat.card K + 1) := by sorry
