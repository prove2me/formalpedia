-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_33fe1755_151f_4b39_a9dc_13183099c0e1_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_33fe1755_151f_4b39_a9dc_13183099c0e1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:19:57.812957+00:00
-- url     : https://prove2.me/theorems/f7f91e8c-5069-473d-a1c5-2fecc5af85f8
-- title:
--   Count the edges of an edge-maximal planar graph
-- statement:
--   An edge-maximal simple planar graph on at least three vertices has exactly 3|V|−6 edges, with a decidable adjacency relation supplied for the finite edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_33fe1755_151f_4b39_a9dc_13183099c0e1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      M ≤ N → HasPlanarDrawingOn N → N = M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (dM : DecidableRel M.Adj),
      (letI : DecidableRel M.Adj := dM;
        M.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
