-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_certificate__p2m_2b02d0f4_e4a5_4246_8c79_3e972b456778_a2
-- name    : WilliamsonShmoys.maximal_planar_face_certificate__p2m_2b02d0f4_e4a5_4246_8c79_3e972b456778_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:54:29.878011+00:00
-- url     : https://prove2.me/theorems/be551f10-f0c9-4808-ad70-62595a008c11
-- title:
--   Finite triangular face certificate for a maximal planar drawing
-- statement:
--   Produce a finite set of faces and their lengths for the drawing. Establish that each edge contributes two face sides, that the vertex-edge-face counts satisfy Euler’s formula, and that maximality makes every face triangular. The final sum identity records the resulting total triangular face length. The hypothesis of at least three vertices preserves the boundary conditions for the triangulation argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_certificate__p2m_2b02d0f4_e4a5_4246_8c79_3e972b456778_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    letI : DecidableRel N.Adj := Classical.decRel N.Adj
    ∃ (F : Type) (_ : Fintype F) (length : F → ℕ),
      (∑ f : F, (length f : ℤ) = 2 * (N.edgeFinset.card : ℤ)) ∧
      ((Fintype.card V : ℤ) - (N.edgeFinset.card : ℤ) + (Fintype.card F : ℤ) = 2) ∧
      (∀ f : F, length f = 3) ∧
      ((∑ f : F, (length f : ℤ)) = 3 * (Fintype.card F : ℤ)) := by sorry
