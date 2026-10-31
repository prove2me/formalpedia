-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count__p2m_1129f324_ed56_4814_b878_03ab3968bf96_a1
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_1129f324_ed56_4814_b878_03ab3968bf96_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:26:28.732114+00:00
-- url     : https://prove2.me/theorems/69a4b515-b2d1-4c44-a03e-fe4ffa3a8acf
-- title:
--   A drawable graph has an exact edge-count triangulation extension
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type of size at least three can be extended, on the same vertices, to a crossing-free drawing whose graph has exactly 3|V|−6 edges. This is the planar augmentation and Euler-counting step needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_1129f324_ed56_4814_b878_03ab3968bf96_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
