-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_7bba71c9_ccd8_4c5e_9f36_6c106eba0d6c_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_7bba71c9_ccd8_4c5e_9f36_6c106eba0d6c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:31:23.848185+00:00
-- url     : https://prove2.me/theorems/88f6e318-47fb-49e3-83e2-88b806f3a0ca
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A simple graph on at least three vertices that is maximal among graphs admitting the given crossing-free drawing predicate has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_7bba71c9_ccd8_4c5e_9f36_6c106eba0d6c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
     H.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  sorry
