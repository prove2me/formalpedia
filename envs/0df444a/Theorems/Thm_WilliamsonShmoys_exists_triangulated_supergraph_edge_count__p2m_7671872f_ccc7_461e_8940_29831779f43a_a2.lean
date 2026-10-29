-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_supergraph_edge_count__p2m_7671872f_ccc7_461e_8940_29831779f43a_a2
-- name    : WilliamsonShmoys.exists_triangulated_supergraph_edge_count__p2m_7671872f_ccc7_461e_8940_29831779f43a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:46:32.349283+00:00
-- url     : https://prove2.me/theorems/f2fb1831-691e-40af-ac91-203f3ac5cf19
-- title:
--   Planar completion with maximal edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices can be extended on the same vertex type to a drawable graph with exactly 3|V|−6 edges. Choose a drawable supergraph with the largest edge set among the finitely many supergraphs, then establish the maximal planar edge count by triangulation and Euler's formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_triangulated_supergraph_edge_count__p2m_7671872f_ccc7_461e_8940_29831779f43a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V, H ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
