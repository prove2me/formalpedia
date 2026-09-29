-- Prove2me | Definitions.Def_ClassicalGaps_orientedIncMatrix
-- name    : ClassicalGaps_orientedIncMatrix
-- status  : Definition
-- author  : @Rizwan G Mir
-- created : 2026-09-24T20:21:59.131094+00:00
-- url     : https://prove2.me/theorems/fe52f806-760b-4aad-8f04-a28110b6a800
-- title:
--   Oriented (signed) incidence matrix of a simple graph
-- statement:
--   The signed incidence matrix of a finite simple graph G, using an arbitrary vertex ordering from Fintype.equivFin to orient each edge. Fills the gap flagged in Mathlib's SimpleGraph.IncMatrix TODO ('Define the oriented incidence matrices for oriented graphs').

import Mathlib

open Classical

namespace ClassicalGaps

/-- The oriented (signed) incidence matrix of a finite simple graph `G`, using the
arbitrary linear order on `V` coming from `Fintype.equivFin`. The `(i, e)` entry is
`1` if `i` is the "smaller-indexed" endpoint of edge `e`, `-1` if `i` is the
"larger-indexed" endpoint, and `0` if `i` is not an endpoint of `e` or `e` is not an
edge of `G`. This fills the gap flagged in Mathlib's `SimpleGraph.IncMatrix` TODO
("Define the oriented incidence matrices for oriented graphs"). -/
noncomputable def orientedIncMatrix {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V (Sym2 V) ℝ :=
  Matrix.of fun i e =>
    if h : i ∈ e ∧ e ∈ G.edgeSet then
      if (Fintype.equivFin V i).val < (Fintype.equivFin V (Sym2.Mem.other' h.1)).val then 1 else -1
    else 0

end ClassicalGaps


