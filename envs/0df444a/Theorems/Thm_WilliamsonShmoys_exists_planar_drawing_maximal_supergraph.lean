-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_drawing_maximal_supergraph
-- name    : WilliamsonShmoys.exists_planar_drawing_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:35:24.478994+00:00
-- url     : https://prove2.me/theorems/221a65d5-7740-4f04-ae52-d40c0c46daae
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   A connected graph with a crossing-free drawing on a finite ordered vertex type has a drawable supergraph on the same vertices that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_drawing_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hconn : Q.Connected) :
    ∃ M : SimpleGraph V,
      Q ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ R : SimpleGraph V,
        M ≤ R →
        WilliamsonShmoys.HasPlanarDrawingOn R →
        R ≤ M := by sorry
