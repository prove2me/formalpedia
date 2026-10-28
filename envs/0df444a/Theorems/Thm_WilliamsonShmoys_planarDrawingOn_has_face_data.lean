-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_has_face_data
-- name    : WilliamsonShmoys.planarDrawingOn_has_face_data
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T05:14:45.641991+00:00
-- url     : https://prove2.me/theorems/6dffd1fb-9a64-460b-b1e9-7c38041cdb87
-- title:
--   Finite face data for a connected planar drawing
-- statement:
--   A connected graph with at least three vertices and the supplied crossing-free drawing has finite face data satisfying Euler’s equation, total boundary length twice the edge count, and boundary length at least three for every face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open scoped BigOperators

theorem WilliamsonShmoys.planarDrawingOn_has_face_data
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : Y.Connected)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ (faces : ℕ) (boundaryLength : Fin faces → ℕ),
      Fintype.card V + faces = Y.edgeSet.ncard + 2 ∧
      (∑ f : Fin faces, boundaryLength f) = 2 * Y.edgeSet.ncard ∧
      ∀ f, 3 ≤ boundaryLength f := by sorry
