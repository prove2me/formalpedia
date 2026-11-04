-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_1cbebd7a_cbfe_40cb_8e61_899ac9ec9081_a3
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_1cbebd7a_cbfe_40cb_8e61_899ac9ec9081_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:56:05.7312+00:00
-- url     : https://prove2.me/theorems/6fbbf826-2147-4da9-aa49-9b6333f29881
-- title:
--   Same-vertex triangulation extension of a planar drawing
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices is contained on the same vertex set in a drawable graph with exactly 3|V|−6 edges. The child explicitly carries the decidable-adjacency instance needed to form the edge finset of the extended graph. The parent applies maximality to show the extension equals the original graph, yielding the target count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_1cbebd7a_cbfe_40cb_8e61_899ac9ec9081_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      ∃ (hKd : DecidableRel K.Adj),
        (letI : DecidableRel K.Adj := hKd;
          K.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
