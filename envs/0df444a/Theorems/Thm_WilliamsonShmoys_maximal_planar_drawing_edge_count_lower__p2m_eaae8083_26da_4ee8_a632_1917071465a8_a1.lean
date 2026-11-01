-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_eaae8083_26da_4ee8_a632_1917071465a8_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_eaae8083_26da_4ee8_a632_1917071465a8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:12:24.90417+00:00
-- url     : https://prove2.me/theorems/1cb61011-99ad-4f9a-a1ee-f080a0059de3
-- title:
--   Lower edge count for a maximal planar drawing
-- statement:
--   A maximal graph admitting the specified planar drawing on a fixed vertex type of at least three vertices has at least 3|V|−6 edges. A proof route is to extend the drawing through nontriangular faces while preserving the vertex set; maximality rules out any further drawable edge, forcing triangular faces. Euler’s formula and face-edge incidence counting then give the bound. The main remaining obligation is formalizing this extension and face argument for the given arc-based drawing definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_eaae8083_26da_4ee8_a632_1917071465a8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    3 * Fintype.card V <= L.edgeFinset.card + 6 := by sorry
