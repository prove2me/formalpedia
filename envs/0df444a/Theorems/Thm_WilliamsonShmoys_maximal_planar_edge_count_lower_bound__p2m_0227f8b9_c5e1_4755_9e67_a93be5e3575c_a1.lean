-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_0227f8b9_c5e1_4755_9e67_a93be5e3575c_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_0227f8b9_c5e1_4755_9e67_a93be5e3575c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:06:45.003689+00:00
-- url     : https://prove2.me/theorems/aa58f2fb-648b-4f0e-9893-f1e72ffeb0ae
-- title:
--   Maximal planar edge count lower bound
-- statement:
--   A graph with a crossing-free drawing that is maximal under drawable supergraphs on the same vertex type has at least 3|V|−6 edges when |V|≥3. Use maximality to show the drawing's faces can be triangulated only if they are already triangles, then apply Euler's formula and count edge-sides. Together with the upper bound, this yields the target equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_0227f8b9_c5e1_4755_9e67_a93be5e3575c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hmax : forall R : SimpleGraph V,
      (forall {u v : V}, Q.Adj u v -> R.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn R ->
      R = Q) :
    letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
    3 * Fintype.card V <= Q.edgeFinset.card + 6 := by sorry
