-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_maximal_extension__p2m_669c86c2_d502_40df_b2a7_d12de81131b5_a1
-- name    : WilliamsonShmoys.planarDrawing_maximal_extension__p2m_669c86c2_d502_40df_b2a7_d12de81131b5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:47:00.755268+00:00
-- url     : https://prove2.me/theorems/131fddda-53be-4336-ab67-f2e30cf87311
-- title:
--   Maximal planar extension on the same vertices
-- statement:
--   Every graph with a planar drawing is contained, on the same finite vertex type, in a graph with a planar drawing that has no strictly larger planar supergraph on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_maximal_extension__p2m_669c86c2_d502_40df_b2a7_d12de81131b5_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) : ∃ M : SimpleGraph V, LE.le L M ∧ HasPlanarDrawingOn M ∧ ∀ N : SimpleGraph V, LE.le M N → HasPlanarDrawingOn N → N = M := by sorry
