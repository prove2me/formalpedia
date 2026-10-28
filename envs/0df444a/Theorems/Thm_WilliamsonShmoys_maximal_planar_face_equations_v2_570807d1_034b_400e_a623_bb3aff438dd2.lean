-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_equations_v2_570807d1_034b_400e_a623_bb3aff438dd2
-- name    : WilliamsonShmoys.maximal_planar_face_equations_v2_570807d1_034b_400e_a623_bb3aff438dd2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T12:58:13.03982+00:00
-- url     : https://prove2.me/theorems/a38de9d7-54e3-4fc8-b142-f310d49ad7e3
-- title:
--   Euler and incidence equations for a maximal planar drawing
-- statement:
--   For a finite linearly ordered vertex type with at least three vertices, a graph with a planar drawing that is maximal among drawable supergraphs has a face count satisfying Euler’s equation and the triangular face-edge incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_face_equations_v2_570807d1_034b_400e_a623_bb3aff438dd2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : forall K : SimpleGraph V, N.edgeSet ⊆ K.edgeSet -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = N)
    (hCard : 3 <= Fintype.card V) :
    exists f : Nat, Fintype.card V + f = N.edgeSet.ncard + 2 ∧ 3 * f = 2 * N.edgeSet.ncard := by sorry
