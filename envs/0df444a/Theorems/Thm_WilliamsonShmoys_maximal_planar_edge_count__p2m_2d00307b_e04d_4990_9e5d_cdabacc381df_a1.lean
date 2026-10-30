-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_2d00307b_e04d_4990_9e5d_cdabacc381df_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_2d00307b_e04d_4990_9e5d_cdabacc381df_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:32:08.618136+00:00
-- url     : https://prove2.me/theorems/45858051-39d1-461c-bf97-6d18e2a89002
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A simple graph on at least three vertices that admits the specified planar drawing and is inclusion-maximal among drawable supergraphs on the same vertex set has exactly 3|V|−6 edges. A proof proceeds through the face structure of a maximal planar drawing and Euler’s formula; the lower bound handles the small-vertex boundary cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_2d00307b_e04d_4990_9e5d_cdabacc381df_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
