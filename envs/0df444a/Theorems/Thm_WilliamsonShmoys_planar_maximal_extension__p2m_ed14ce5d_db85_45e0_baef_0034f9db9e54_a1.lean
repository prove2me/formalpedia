-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_ed14ce5d_db85_45e0_baef_0034f9db9e54_a1
-- name    : WilliamsonShmoys.planar_maximal_extension__p2m_ed14ce5d_db85_45e0_baef_0034f9db9e54_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:16:18.0405+00:00
-- url     : https://prove2.me/theorems/be88e34f-afdc-4940-bc2f-5ba7174bcc58
-- title:
--   Finite maximal drawable extension
-- statement:
--   This child supplies the finite-order step used by the parent: among drawable supergraphs of U on the same finite vertex type, choose one maximal under inclusion. It follows from finiteness of the set of simple graphs on V and does not add a topological claim. A direct proof route is to maximize edge-set cardinality among drawable supergraphs; any proper drawable extension would have more edges. The parent still needs the separate maximal-planar edge-count theorem.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_extension__p2m_ed14ce5d_db85_45e0_baef_0034f9db9e54_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ W : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn W ∧ U ≤ W ∧
        ∀ X : SimpleGraph V,
          WilliamsonShmoys.HasPlanarDrawingOn X → W ≤ X → X ≤ W := by sorry
