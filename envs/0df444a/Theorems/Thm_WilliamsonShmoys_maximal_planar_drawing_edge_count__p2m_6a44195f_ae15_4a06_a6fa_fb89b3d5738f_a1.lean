-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_6a44195f_ae15_4a06_a6fa_fb89b3d5738f_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6a44195f_ae15_4a06_a6fa_fb89b3d5738f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:22:20.05819+00:00
-- url     : https://prove2.me/theorems/5fb904eb-fef4-45c3-b974-7b95702b51b3
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   Every maximal planar simple graph on at least three vertices has exactly 3|V|−6 edges. The proof must turn the given crossing-free drawing into a plane embedding, use maximality to establish that all faces are triangular, and apply Euler's formula and face-edge incidence counting. This is a meaningful reduction because it isolates the graph-topological edge-count theorem; the parent then follows by arithmetic. The boundary case of exactly three vertices is included and forces the triangle. A concrete independent proof route is the plane-embedding argument just described; the remaining core obligation is formalizing that argument for the supplied topological-arc definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6a44195f_ae15_4a06_a6fa_fb89b3d5738f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hmax : forall H : SimpleGraph V, K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
