-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_completion_20261026
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_completion_20261026
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T01:06:38.522458+00:00
-- url     : https://prove2.me/theorems/69cfd00a-df39-4db4-beca-538dcb37deb3
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. This supplies the quantitative conclusion after the first child supplies maximality. The proof route is to use the crossing-free drawing to establish the standard maximal-planar structure: the graph is connected and every face is triangular, since an omitted edge could otherwise be added inside a face. Euler’s formula and counting each face boundary edge twice yield the result. The boundary |V| = 3 is the triangle. Formalizing this from the packaged continuous-arc drawing definition is the remaining core topological obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_for_completion_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
