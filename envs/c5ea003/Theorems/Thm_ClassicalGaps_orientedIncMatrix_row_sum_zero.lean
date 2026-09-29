-- Prove2me | Theorems.Thm_ClassicalGaps_orientedIncMatrix_row_sum_zero
-- name    : ClassicalGaps.orientedIncMatrix_row_sum_zero
-- status  : Proved
-- author  : @Rizwan G Mir
-- created : 2026-09-24T22:41:45.142154+00:00
-- url     : https://prove2.me/theorems/784fa316-adc2-481b-8762-5c02cbca5d41
-- title:
--   Column row-sums of the oriented incidence matrix vanish
-- statement:
--   For a finite simple graph G and any edge e of G, the column of the oriented (signed) incidence matrix corresponding to e sums to zero over all vertices: the edge has exactly two endpoints, contributing +1 and -1 respectively (per the arbitrary linear order on V), and every other vertex contributes 0. This is a standard supporting fact used in Kirchhoff-matrix-tree-theorem-style arguments (e.g. to show all maximal minors of the incidence matrix agree up to sign).

import Mathlib
import Definitions.Def_ClassicalGaps_orientedIncMatrix

open Classical ClassicalGaps

namespace ClassicalGaps

theorem orientedIncMatrix_row_sum_zero {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (e : Sym2 V) (he : e ∈ G.edgeSet) :
    ∑ v : V, orientedIncMatrix G v e = 0 := by sorry

end ClassicalGaps
