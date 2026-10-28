-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_7f31c9a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_7f31c9a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T18:48:29.574757+00:00
-- url     : https://prove2.me/theorems/77f664a0-9049-47af-9274-a35bf0bc9e14
-- title:
--   A maximum drawable supergraph has the triangulation edge count
-- statement:
--   If H is drawable and maximizes edge count among drawable supergraphs of K, and there are at least three vertices, then H has exactly 3|V|−6 edges. The proof reduces to showing that such a maximal drawing is a triangulation and applying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_7f31c9a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (H : SimpleGraph V)
    (hKH : ∀ u v, K.Adj u v → H.Adj u v)
    (hDrawH : HasPlanarDrawingOn H)
    (hmax : ∀ G : SimpleGraph V,
      (∀ u v, K.Adj u v → G.Adj u v) →
      HasPlanarDrawingOn G →
      G.edgeSet.ncard ≤ H.edgeSet.ncard) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
