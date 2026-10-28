-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_face_count_c76468fe
-- name    : WilliamsonShmoys.maximal_planar_edge_face_count_c76468fe
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T20:03:30.812583+00:00
-- url     : https://prove2.me/theorems/92703542-9701-452c-b6a8-363f18bf7214
-- title:
--   Euler and triangular faces for maximal planar drawings
-- statement:
--   For a finite simple graph with at least three vertices, a crossing-free drawing that is maximal among drawable supergraphs has a face count satisfying Euler’s relation and triangular face-incidence counting. Here the witness equations use the convention that each edge contributes two face incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_face_count_c76468fe {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) (hCard : 3 ≤ Fintype.card V) : ∃ f : Nat, Fintype.card V + f = H.edgeSet.ncard + 2 ∧ 3 * f = 2 * H.edgeSet.ncard := by sorry
