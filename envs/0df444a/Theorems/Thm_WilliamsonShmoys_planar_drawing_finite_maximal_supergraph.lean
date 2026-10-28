-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_supergraph
-- name    : WilliamsonShmoys.planar_drawing_finite_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:31:38.482807+00:00
-- url     : https://prove2.me/theorems/3c80615f-4f33-43d0-bb7e-0dc692714eb0
-- title:
--   Extend a planar drawing to a finite maximal planar supergraph
-- statement:
--   A planar graph on a finite ordered vertex type has an inclusion-maximal planar supergraph on the same vertices, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_finite_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists fun K : SimpleGraph V =>
      And (H <= K)
        (And (WilliamsonShmoys.HasPlanarDrawingOn K)
          (And (forall K' : SimpleGraph V, K <= K' ->
            WilliamsonShmoys.HasPlanarDrawingOn K' -> K' = K)
            (H.edgeSet.ncard <= K.edgeSet.ncard))) := by sorry
