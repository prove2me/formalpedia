-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_boundary_count__p2m_e743f516_2fe6_4f90_ae81_e51127ac517d_a2
-- name    : WilliamsonShmoys.planar_drawing_face_boundary_count__p2m_e743f516_2fe6_4f90_ae81_e51127ac517d_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:37:26.095792+00:00
-- url     : https://prove2.me/theorems/d2113d71-f40c-40c2-aa83-a71917282bca
-- title:
--   Face boundary counts from a planar drawing
-- statement:
--   Extract the facial boundary lengths of the connected simple plane drawing. Each length is at least three, the lengths sum to twice the number of edges, and Euler's formula gives the vertex-face-edge relation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

theorem WilliamsonShmoys.planar_drawing_face_boundary_count__p2m_e743f516_2fe6_4f90_ae81_e51127ac517d_a2 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) [DecidableRel M.Adj] (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hconn : M.Connected) (hcard : 3 ≤ Fintype.card V) : ∃ lengths : List ℕ, (∀ ℓ ∈ lengths, 3 ≤ ℓ) ∧ lengths.sum = 2 * M.edgeFinset.card ∧ Fintype.card V + lengths.length = M.edgeFinset.card + 2 := by sorry
