-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_certificate_retry_917de119
-- name    : WilliamsonShmoys.planar_drawing_euler_certificate_retry_917de119
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T00:08:41.782516+00:00
-- url     : https://prove2.me/theorems/50c6712f-de3c-41bd-a070-9dba7c005bf5
-- title:
--   Finite face certificate for a connected planar drawing
-- statement:
--   The given connected simple graph drawing admits finitely many faces whose boundary lengths are all at least three, sum to twice the number of edges, and satisfy Euler’s vertex-face equation. The condition of at least three vertices rules out the small connected graph exceptions to the face-length bound. The new work is constructing facial walks from the drawing, handling bridges, and proving the Euler and incidence equations. A proof route is to derive the finite plane embedding from the arcs, construct its facial walks, and apply the connected plane graph Euler formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_certificate_retry_917de119
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 <= Fintype.card V) :
    ∃ (F : Type) (instF : Fintype F) (boundaryLength : F → ℕ),
      (∀ f : F, 3 <= boundaryLength f) ∧
      Finset.sum (@Finset.univ F instF) boundaryLength = 2 * G.edgeSet.ncard ∧
      Fintype.card V + @Fintype.card F instF = G.edgeSet.ncard + 2 := by sorry
