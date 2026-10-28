-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_data_from_planar_drawing
-- name    : WilliamsonShmoys.face_data_from_planar_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T13:47:09.708952+00:00
-- url     : https://prove2.me/theorems/e8c8adf8-7489-462e-af5b-c6cb37e0c8c5
-- title:
--   Finite face data from a connected planar drawing
-- statement:
--   Extract a finite face type and a natural boundary length for every face of the supplied drawing. The lengths satisfy Euler’s equation, each is at least three, and their sum is twice the number of edges. This removes the topological face extraction and counting from the parent, which then obtains the target inequality by finite summation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.face_data_from_planar_drawing {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hconn : H.Connected) (hcard : 3 ≤ Fintype.card V) : ∃ (F : Type) (inst : Fintype F) (length : F → ℕ), @Fintype.card V inferInstance + @Fintype.card F inst = H.edgeSet.ncard + 2 ∧ (∀ f, 3 ≤ length f) ∧ @Finset.sum F ℕ (inferInstance : AddCommMonoid ℕ) (@Finset.univ F inst) length = 2 * H.edgeSet.ncard := by sorry
