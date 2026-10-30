-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_extension__p2m_bd5a0062_468c_43aa_a2a2_0a304df33140_a2
-- name    : WilliamsonShmoys.maximal_planar_supergraph_extension__p2m_bd5a0062_468c_43aa_a2a2_0a304df33140_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:14:14.061161+00:00
-- url     : https://prove2.me/theorems/a04df878-b6ad-4681-a0ee-bcd4750a4cbc
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every finite planar graph has an inclusion-maximal planar supergraph on the same vertex type. Maximality is among planar supergraphs under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_extension__p2m_bd5a0062_468c_43aa_a2a2_0a304df33140_a2 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ (∀ G : SimpleGraph V, H ≤ G → WilliamsonShmoys.HasPlanarDrawingOn G → G = H) := by sorry
