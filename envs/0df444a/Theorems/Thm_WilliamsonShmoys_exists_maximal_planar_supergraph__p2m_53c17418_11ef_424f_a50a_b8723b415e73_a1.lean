-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_53c17418_11ef_424f_a50a_b8723b415e73_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_53c17418_11ef_424f_a50a_b8723b415e73_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:47:42.765949+00:00
-- url     : https://prove2.me/theorems/17ee7912-1576-447c-9193-038c59d3a9f3
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every finite drawn planar graph has a same-vertex planar supergraph that is maximal among planar supergraphs of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_53c17418_11ef_424f_a50a_b8723b415e73_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, H ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
