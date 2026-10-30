-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_5172cebe_7d77_4b25_aa7c_10802cca0895_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_5172cebe_7d77_4b25_aa7c_10802cca0895_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:32:30.346437+00:00
-- url     : https://prove2.me/theorems/e3290709-cdc2-4958-9fab-02f715f97993
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable simple graph on at least three vertices that cannot be extended by adding drawable edges has exactly three times its number of vertices minus six edges. The decidable-adjacency instance is included so the edge finset is defined.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_5172cebe_7d77_4b25_aa7c_10802cca0895_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  sorry
