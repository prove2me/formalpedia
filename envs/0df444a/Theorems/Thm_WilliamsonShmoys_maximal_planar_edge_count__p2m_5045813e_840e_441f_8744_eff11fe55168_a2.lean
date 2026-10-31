-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5045813e_840e_441f_8744_eff11fe55168_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_5045813e_840e_441f_8744_eff11fe55168_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:47:06.233239+00:00
-- url     : https://prove2.me/theorems/8e3b1f8a-4617-463b-ae07-33ab92d25c24
-- title:
--   Maximal drawable graphs have the planar triangulation edge count
-- statement:
--   An inclusion-maximal drawable simple graph with at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_5045813e_840e_441f_8744_eff11fe55168_a2 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hMax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) (hCard : 3 ≤ Fintype.card V) : K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
