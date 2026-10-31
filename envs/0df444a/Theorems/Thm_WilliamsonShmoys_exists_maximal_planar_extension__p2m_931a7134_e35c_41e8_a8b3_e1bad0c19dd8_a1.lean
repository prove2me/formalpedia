-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_931a7134_e35c_41e8_a8b3_e1bad0c19dd8_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_extension__p2m_931a7134_e35c_41e8_a8b3_e1bad0c19dd8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:38:58.839991+00:00
-- url     : https://prove2.me/theorems/b14cb1c9-e46e-498d-93f0-e98be9265b47
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs under graph inclusion. Choose a planar supergraph with a largest edge set; any planar supergraph containing it must be equal to it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_extension__p2m_931a7134_e35c_41e8_a8b3_e1bad0c19dd8_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ W : SimpleGraph V, G ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧ ∀ H : SimpleGraph V, W ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = W := by sorry
