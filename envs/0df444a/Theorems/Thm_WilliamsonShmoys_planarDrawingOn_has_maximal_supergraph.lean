-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_has_maximal_supergraph
-- name    : WilliamsonShmoys.planarDrawingOn_has_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:47:29.856851+00:00
-- url     : https://prove2.me/theorems/c868dcdd-428f-4939-8970-72edfa0abeb5
-- title:
--   Every drawable graph has a maximal drawable supergraph
-- statement:
--   For a finite ordered vertex type, any drawable graph has a drawable supergraph that is maximal among drawable supergraphs on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_has_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ S : SimpleGraph V, R ≤ S ∧
      WilliamsonShmoys.HasPlanarDrawingOn S ∧
      ∀ T : SimpleGraph V, S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S := by sorry
