-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_edge_count_extension
-- name    : WilliamsonShmoys.exists_planar_edge_count_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:10:47.990856+00:00
-- url     : https://prove2.me/theorems/0fe52394-5882-4e40-a5d1-7128b9a37eac
-- title:
--   Planar extension with the maximal planar edge count
-- statement:
--   Every graph with a supplied crossing-free drawing on a finite ordered vertex set of size at least three has a planar supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_edge_count_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ J : SimpleGraph V,
      HasPlanarDrawingOn J ∧ G.edgeSet ⊆ J.edgeSet ∧
        J.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
