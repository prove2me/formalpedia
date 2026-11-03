-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximalPlanarDrawingOn_edge_count_upper__p2m_341f0f70_acb5_465d_8404_ec7db43234c5_a1
-- name    : WilliamsonShmoys.maximalPlanarDrawingOn_edge_count_upper__p2m_341f0f70_acb5_465d_8404_ec7db43234c5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:22:22.620597+00:00
-- url     : https://prove2.me/theorems/241764c0-df01-413a-860c-709c9db3e876
-- title:
--   Upper edge bound for a maximal planar drawing
-- statement:
--   A drawable graph on at least three finite ordered vertices has at most 3|V|−6 edges. The maximality hypothesis is retained to match the parent theorem’s assumptions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximalPlanarDrawingOn_edge_count_upper__p2m_341f0f70_acb5_465d_8404_ec7db43234c5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hmax : forall L : SimpleGraph V, K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) :
    K.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
