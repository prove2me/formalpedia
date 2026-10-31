-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_exact_edge_count__p2m_70a6424f_4889_4ef2_870f_ee6e7e607f96_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion_exact_edge_count__p2m_70a6424f_4889_4ef2_870f_ee6e7e607f96_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:28:15.500659+00:00
-- url     : https://prove2.me/theorems/2cd3ad17-4dba-4e7e-aee4-3660ec319d01
-- title:
--   Triangulated drawable completion has the maximal planar edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices is contained in a drawable graph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_completion_exact_edge_count__p2m_70a6424f_4889_4ef2_870f_ee6e7e607f96_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
