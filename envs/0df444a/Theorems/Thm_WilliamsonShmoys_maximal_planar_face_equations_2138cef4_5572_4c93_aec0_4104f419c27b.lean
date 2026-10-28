-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_equations_2138cef4_5572_4c93_aec0_4104f419c27b
-- name    : WilliamsonShmoys.maximal_planar_face_equations_2138cef4_5572_4c93_aec0_4104f419c27b
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T02:54:25.058135+00:00
-- url     : https://prove2.me/theorems/1fead81e-0a94-499a-9b48-6a9c4e5278ad
-- title:
--   Euler and triangular-face equations for a maximal planar drawing
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable edge-supergraphs has a face count satisfying Euler’s equation and the triangular-face incidence equation. The first equation records connected planar Euler counting; the second follows because maximality forces every face to be a triangle. Together these equations give the target edge count. A proof can construct the plane embedding from the supplied arcs, use maximality to establish connectedness and rule out faces with more than three boundary edges, and then apply Euler’s formula and face-edge incidence counting. This isolates the topological embedding and triangulation argument from the parent’s arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_equations_2138cef4_5572_4c93_aec0_4104f419c27b
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L → L.edgeSet ⊆ K.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      (Fintype.card V + f = K.edgeSet.ncard + 2) ∧
      (3 * f = 2 * K.edgeSet.ncard) := by sorry
