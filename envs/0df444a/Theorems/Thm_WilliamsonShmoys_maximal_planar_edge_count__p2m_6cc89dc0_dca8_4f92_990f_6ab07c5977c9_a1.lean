-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_6cc89dc0_dca8_4f92_990f_6ab07c5977c9_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_6cc89dc0_dca8_4f92_990f_6ab07c5977c9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:13:26.417673+00:00
-- url     : https://prove2.me/theorems/d20eded3-dab8-49a7-8ba9-801d4ba77b67
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   An inclusion-maximal graph with a planar drawing on at least three finite vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_6cc89dc0_dca8_4f92_990f_6ab07c5977c9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : LE.le 3 (Fintype.card V))
    (hT : HasPlanarDrawingOn T)
    (hmax : forall T' : SimpleGraph V, LE.le T T' -> HasPlanarDrawingOn T' -> T' = T) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
