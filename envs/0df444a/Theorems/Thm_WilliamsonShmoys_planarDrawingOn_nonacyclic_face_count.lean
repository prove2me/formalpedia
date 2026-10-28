-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_nonacyclic_face_count
-- name    : WilliamsonShmoys.planarDrawingOn_nonacyclic_face_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T09:11:03.498686+00:00
-- url     : https://prove2.me/theorems/5218b1c3-49ee-4845-a092-e63d33b07a5a
-- title:
--   Euler face count and degree bound from a non-acyclic planar drawing
-- statement:
--   A finite connected simple graph with at least three vertices and a cycle, drawn by the supplied noncrossing arcs, has a natural-number face count satisfying Euler's equation and the total face-boundary length bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_nonacyclic_face_count
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hCard : 3 ≤ Fintype.card V)
    (hconn : X.Connected)
    (hcyclic : ¬ X.IsAcyclic) :
    ∃ f : ℕ, Fintype.card V + f = X.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * X.edgeSet.ncard := by sorry
