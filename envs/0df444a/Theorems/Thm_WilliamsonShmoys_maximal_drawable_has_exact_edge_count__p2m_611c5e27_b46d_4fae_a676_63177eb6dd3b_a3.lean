-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_has_exact_edge_count__p2m_611c5e27_b46d_4fae_a676_63177eb6dd3b_a3
-- name    : WilliamsonShmoys.maximal_drawable_has_exact_edge_count__p2m_611c5e27_b46d_4fae_a676_63177eb6dd3b_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:37:15.648079+00:00
-- url     : https://prove2.me/theorems/f4c5a554-b014-419c-ba42-5bef32be5934
-- title:
--   Maximal drawable graphs have the triangulation edge count
-- statement:
--   A drawable graph on a finite linearly ordered vertex type with at least three vertices has exactly three times the vertex count minus six edges if every drawable supergraph on that type is contained in it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_has_exact_edge_count__p2m_611c5e27_b46d_4fae_a676_63177eb6dd3b_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hPlanar : HasPlanarDrawingOn K)
    (hMaximal : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H ≤ K) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    K.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
