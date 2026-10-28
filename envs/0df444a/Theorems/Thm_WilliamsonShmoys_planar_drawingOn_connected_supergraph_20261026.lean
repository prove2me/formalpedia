-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_connected_supergraph_20261026
-- name    : WilliamsonShmoys.planar_drawingOn_connected_supergraph_20261026
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T01:30:14.443033+00:00
-- url     : https://prove2.me/theorems/062fd0c6-2b61-4d51-95f1-a62f8e42093d
-- title:
--   Connected planar supergraph on the same vertices
-- statement:
--   Any finite graph with the supplied crossing-free drawing and at least three vertices has a connected planar supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawingOn_connected_supergraph_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K' : SimpleGraph V,
      K ≤ K' ∧ K'.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K' := by sorry
