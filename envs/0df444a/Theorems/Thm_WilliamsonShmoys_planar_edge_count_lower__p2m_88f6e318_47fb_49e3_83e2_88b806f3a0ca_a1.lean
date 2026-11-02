-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_lower__p2m_88f6e318_47fb_49e3_83e2_88b806f3a0ca_a1
-- name    : WilliamsonShmoys.planar_edge_count_lower__p2m_88f6e318_47fb_49e3_83e2_88b806f3a0ca_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:50:18.140359+00:00
-- url     : https://prove2.me/theorems/285fd92f-ac7f-4984-a234-6720989533e3
-- title:
--   Edge lower bound for a maximal finite topological planar drawing
-- statement:
--   A maximal graph among those satisfying `HasPlanarDrawingOn`, with at least three vertices, has at least `3|V| − 6` edges. The proof must show that maximality forces a triangulated plane embedding, then apply Euler’s formula and count face-edge incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_lower__p2m_88f6e318_47fb_49e3_83e2_88b806f3a0ca_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
     3 * Fintype.card V <= H.edgeFinset.card + 6) := by
  sorry
