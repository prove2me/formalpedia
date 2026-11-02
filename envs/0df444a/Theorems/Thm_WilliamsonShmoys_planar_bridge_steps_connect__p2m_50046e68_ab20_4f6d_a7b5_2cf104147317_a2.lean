-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_bridge_steps_connect__p2m_50046e68_ab20_4f6d_a7b5_2cf104147317_a2
-- name    : WilliamsonShmoys.planar_bridge_steps_connect__p2m_50046e68_ab20_4f6d_a7b5_2cf104147317_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:17:36.998199+00:00
-- url     : https://prove2.me/theorems/6759599f-0df8-4b6f-bc89-5739bb0b46dc
-- title:
--   Iterate planar bridge extensions to connect a drawing
-- statement:
--   If every disconnected graph on the fixed finite vertex type with a crossing-free drawing admits a new planar bridge extension, then any such drawing can be extended to a connected planar supergraph. Repeatedly adding a previously absent edge strictly increases the finite edge set, so the augmentation terminates.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_bridge_steps_connect__p2m_50046e68_ab20_4f6d_a7b5_2cf104147317_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hstep : ∀ G : SimpleGraph V, HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ u v : V, ∃ H : SimpleGraph V,
        ¬ G.Adj u v ∧ G ≤ H ∧ H.Adj u v ∧ HasPlanarDrawingOn H) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
