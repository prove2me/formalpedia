-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_e8d830f7_8876_4fbd_9d43_eb90e96cd3c0_a1
-- name    : WilliamsonShmoys.maximal_planar_extension__p2m_e8d830f7_8876_4fbd_9d43_eb90e96cd3c0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:24:56.242143+00:00
-- url     : https://prove2.me/theorems/ed7e5ecf-79d4-4fb2-a080-a3796f5af948
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertex set that has no proper drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_extension__p2m_e8d830f7_8876_4fbd_9d43_eb90e96cd3c0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H := by sorry
