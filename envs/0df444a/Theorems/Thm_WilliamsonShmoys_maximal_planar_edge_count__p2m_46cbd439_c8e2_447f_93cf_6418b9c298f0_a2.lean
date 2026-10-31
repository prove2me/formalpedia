-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_46cbd439_c8e2_447f_93cf_6418b9c298f0_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_46cbd439_c8e2_447f_93cf_6418b9c298f0_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:31:09.86723+00:00
-- url     : https://prove2.me/theorems/1e4fc4c6-43c4-4ae0-af53-1d46a400a440
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A finite simple graph on at least three vertices that is maximal among planar supergraphs on the same vertex type has exactly 3n−6 edges. The drawing and maximality hypotheses support the argument that every face is triangular; Euler’s formula and counting edge incidences then give the equality, including the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_46cbd439_c8e2_447f_93cf_6418b9c298f0_a2 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) (hCard : 3 ≤ Fintype.card V) (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N) : N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
