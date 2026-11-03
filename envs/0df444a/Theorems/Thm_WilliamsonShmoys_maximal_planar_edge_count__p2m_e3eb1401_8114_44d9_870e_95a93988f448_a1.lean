-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_e3eb1401_8114_44d9_870e_95a93988f448_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_e3eb1401_8114_44d9_870e_95a93988f448_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:26:02.672345+00:00
-- url     : https://prove2.me/theorems/5080cd2f-42f1-4d04-bf29-e50a32f61412
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable graph on a finite linearly ordered vertex type with at least three vertices, maximal among drawable graphs on that same vertex type under edge inclusion, has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_e3eb1401_8114_44d9_870e_95a93988f448_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, HasPlanarDrawingOn M →
      (∀ u v, L.Adj u v → M.Adj u v) →
      ∀ u v, M.Adj u v → L.Adj u v) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
     3 * Fintype.card V = L.edgeFinset.card + 6) := by sorry
