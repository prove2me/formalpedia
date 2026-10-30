-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_complete_card_le_four__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a2
-- name    : WilliamsonShmoys.planar_complete_card_le_four__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:20:26.249187+00:00
-- url     : https://prove2.me/theorems/5e2c5d47-5385-4c28-8f25-877ce4670fc9
-- title:
--   A planar complete graph has at most four vertices
-- statement:
--   A finite complete graph with a crossing-free drawing under the supplied drawing definition has at most four vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_complete_card_le_four__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcomplete : ∀ u v : V, u ≠ v → H.Adj u v) :
    Fintype.card V ≤ 4 := by sorry
