-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count__p2m_aea893ff_524d_432f_a94f_a28f6a185e5e_a2
-- name    : WilliamsonShmoys.edge_maximal_planar_edge_count__p2m_aea893ff_524d_432f_a94f_a28f6a185e5e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:11:54.755802+00:00
-- url     : https://prove2.me/theorems/8dfa4b72-07b4-4156-b232-5425c6bb73fa
-- title:
--   Edge count of an edge maximal planar graph
-- statement:
--   An edge-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. This isolates the topological argument: maximality gives a triangulation, and Euler’s formula with the face-degree sum gives the equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_edge_count__p2m_aea893ff_524d_432f_a94f_a28f6a185e5e_a2 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hK : HasPlanarDrawingOn K) (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) : K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
