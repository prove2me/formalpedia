-- Prove2me | Theorems.Thm_planarDrawingOn_exists_maximal_supergraph
-- name    : planarDrawingOn_exists_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:29:14.920451+00:00
-- url     : https://prove2.me/theorems/07837d37-a8dd-4c5b-8c94-367c85c86488
-- title:
--   Existence of an inclusion-maximal planar supergraph
-- statement:
--   Every graph with a planar drawing on a finite ordered vertex type is contained in a planar graph on the same vertices that has no strictly larger planar supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem planarDrawingOn_exists_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V, G ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ K : SimpleGraph V, L ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ L := by sorry
