-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_ed86bc60_f31a_467f_bd4d_ab190f9b728c_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_ed86bc60_f31a_467f_bd4d_ab190f9b728c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:14:59.338471+00:00
-- url     : https://prove2.me/theorems/3e744d16-fd12-4405-889b-d7d7bae50b90
-- title:
--   Extend a planar graph to a maximal planar supergraph
-- statement:
--   Every drawable finite simple graph on a finite linearly ordered vertex type is contained in an inclusion-maximal drawable graph on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_ed86bc60_f31a_467f_bd4d_ab190f9b728c_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
