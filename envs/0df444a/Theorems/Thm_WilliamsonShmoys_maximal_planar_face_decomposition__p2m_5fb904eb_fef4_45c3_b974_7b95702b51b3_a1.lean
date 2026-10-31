-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_5fb904eb_fef4_45c3_b974_7b95702b51b3_a1
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition__p2m_5fb904eb_fef4_45c3_b974_7b95702b51b3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:36:39.61216+00:00
-- url     : https://prove2.me/theorems/e194ab00-41b0-4b4f-af08-d9da373e3f16
-- title:
--   Euler and triangular-face equations for a maximal planar drawing
-- statement:
--   For a maximal drawable simple graph on at least three vertices, there is a face count satisfying Euler’s equation and the triangular face-edge incidence equation. These two identities imply the target edge count. The case of three vertices is included: the equations give two faces and three edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_decomposition__p2m_5fb904eb_fef4_45c3_b974_7b95702b51b3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall H : SimpleGraph V, K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K)
    (hV : 3 <= Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by sorry
