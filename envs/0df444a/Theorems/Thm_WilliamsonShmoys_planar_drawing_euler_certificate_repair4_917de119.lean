-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_certificate_repair4_917de119
-- name    : WilliamsonShmoys.planar_drawing_euler_certificate_repair4_917de119
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T00:40:54.60087+00:00
-- url     : https://prove2.me/theorems/d9379f81-7765-45ea-8965-6ac13da482e0
-- title:
--   Finite face certificate for a connected planar drawing
-- statement:
--   Construct finite face-boundary data for the connected planar drawing, with each boundary length at least three, total boundary length twice the number of edges, and Euler’s vertex-face equation. The topological argument must construct facial walks from the supplied arcs and account for bridges. The three-vertex hypothesis preserves the boundary case needed for the minimum face length.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_euler_certificate_repair4_917de119
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 <= Fintype.card V) :
    ∃ (F : Type) (instF : Fintype F) (boundaryLength : F → ℕ),
      (∀ f : F, 3 <= boundaryLength f) ∧
      Finset.sum (@Finset.univ F instF) boundaryLength = 2 * G.edgeSet.ncard ∧
      Fintype.card V + @Fintype.card F instF = G.edgeSet.ncard + 2 := by sorry
