-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_extension__p2m_9379b763_2dc6_43e2_b02a_b18a7334854d_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_extension__p2m_9379b763_2dc6_43e2_b02a_b18a7334854d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:15:16.559291+00:00
-- url     : https://prove2.me/theorems/abce8b2a-47a4-411c-aacc-421d6b13a003
-- title:
--   Extend a planar drawing below the maximal edge bound
-- statement:
--   If a finite graph on at least three vertices has a crossing-free drawing and fewer than 3|V|−6 edges, then some strict supergraph on the same vertices also has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_extension__p2m_9379b763_2dc6_43e2_b02a_b18a7334854d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hdef : M.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ K : SimpleGraph V, M < K ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
