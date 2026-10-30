-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_22eb0949_0e91_449a_8343_64436b0a0efb_a1
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_22eb0949_0e91_449a_8343_64436b0a0efb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:59:37.320671+00:00
-- url     : https://prove2.me/theorems/34323cd1-374d-4357-8256-7d86cba1e73f
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_22eb0949_0e91_449a_8343_64436b0a0efb_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : ∃ T : SimpleGraph V, L ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧ ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T := by sorry
