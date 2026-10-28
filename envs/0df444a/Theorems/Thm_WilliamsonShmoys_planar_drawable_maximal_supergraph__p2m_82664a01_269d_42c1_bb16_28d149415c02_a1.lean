-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_supergraph__p2m_82664a01_269d_42c1_bb16_28d149415c02_a1
-- name    : WilliamsonShmoys.planar_drawable_maximal_supergraph__p2m_82664a01_269d_42c1_bb16_28d149415c02_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:50:18.702797+00:00
-- url     : https://prove2.me/theorems/2e3d33d0-6b5e-40a9-a786-4b1fab836e4e
-- title:
--   Every drawable finite graph has a maximal drawable supergraph
-- statement:
--   On a finite vertex type, every drawable simple graph is contained in a drawable supergraph that has no strictly larger drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawable_maximal_supergraph__p2m_82664a01_269d_42c1_bb16_28d149415c02_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ T : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      R ≤ T ∧
      ∀ U : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn U → T ≤ U → U = T := by sorry
