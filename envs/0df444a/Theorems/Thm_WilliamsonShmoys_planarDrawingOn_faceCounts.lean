-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_faceCounts
-- name    : WilliamsonShmoys.planarDrawingOn_faceCounts
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T11:24:23.208213+00:00
-- url     : https://prove2.me/theorems/49d4ee1d-7c3d-4b51-9e92-2cb277727e00
-- title:
--   Euler and facial incidence counts from a planar drawing
-- statement:
--   A connected finite graph with at least three vertices and a drawing satisfying the packaged predicate has facial boundary lengths satisfying Euler’s equation, total edge-side incidence 2E, and minimum face length three. Prove this by converting the given arcs into a plane embedding and applying the standard connected plane-graph face count; this removes the embedding and facial-walk work from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_faceCounts
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 <= Fintype.card V) :
    ∃ (F : Nat) (faceLength : Fin F → Nat),
      Fintype.card V + F = G.edgeSet.ncard + 2 ∧
      (∑ f : Fin F, faceLength f) = 2 * G.edgeSet.ncard ∧
      ∀ f : Fin F, 3 <= faceLength f := by sorry
