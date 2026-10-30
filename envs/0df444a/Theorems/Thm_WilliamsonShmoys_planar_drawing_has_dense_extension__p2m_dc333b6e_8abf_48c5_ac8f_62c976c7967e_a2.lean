-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_dense_extension__p2m_dc333b6e_8abf_48c5_ac8f_62c976c7967e_a2
-- name    : WilliamsonShmoys.planar_drawing_has_dense_extension__p2m_dc333b6e_8abf_48c5_ac8f_62c976c7967e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:26:51.364793+00:00
-- url     : https://prove2.me/theorems/6630bfc0-6fd3-4ee5-a018-4b73345ede9f
-- title:
--   Every planar drawing has a dense drawable extension
-- statement:
--   Every graph with a planar drawing on a finite ordered vertex set of size at least three is a subgraph of a drawable graph on the same vertices with at least 3|V|−6 edges. At size three, the bound is three edges, attained by K3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_dense_extension__p2m_dc333b6e_8abf_48c5_ac8f_62c976c7967e_a2 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V) (hDraw : HasPlanarDrawingOn P) (hV : 3 ≤ Fintype.card V) : ∃ Q : SimpleGraph V, P ≤ Q ∧ HasPlanarDrawingOn Q ∧ 3 * Fintype.card V ≤ Q.edgeSet.ncard + 6 := by sorry
