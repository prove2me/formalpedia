-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_9eedc9cb_93e3_43ae_9b38_877bad90d9bc_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_9eedc9cb_93e3_43ae_9b38_877bad90d9bc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:07:24.099714+00:00
-- url     : https://prove2.me/theorems/e3d00913-05dd-434d-bc2d-b9a3208fb1a4
-- title:
--   Choose an inclusion-maximal planar supergraph
-- statement:
--   On a finite vertex type, every drawable graph has an inclusion-maximal drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_9eedc9cb_93e3_43ae_9b38_877bad90d9bc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (_ : DecidableRel K.Adj),
      H.edgeFinset ⊆ K.edgeFinset ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ (L : SimpleGraph V) (_ : DecidableRel L.Adj),
        K.edgeFinset ⊂ L.edgeFinset → ¬ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
