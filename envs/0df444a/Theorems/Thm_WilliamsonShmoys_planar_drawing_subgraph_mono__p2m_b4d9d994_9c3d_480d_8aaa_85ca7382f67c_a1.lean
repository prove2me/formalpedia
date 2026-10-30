-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph_mono__p2m_b4d9d994_9c3d_480d_8aaa_85ca7382f67c_a1
-- name    : WilliamsonShmoys.planar_drawing_subgraph_mono__p2m_b4d9d994_9c3d_480d_8aaa_85ca7382f67c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:29:16.991331+00:00
-- url     : https://prove2.me/theorems/535fa532-beed-40e5-b016-9fced59429b7
-- title:
--   Planarity is inherited by subgraphs
-- statement:
--   If B is a subgraph of A on the same vertex type and A has a crossing-free drawing, then B has one too. Keep the drawing witnesses and restrict the edge conditions to B's edges. The child removes the topological restriction step from the parent; a direct proof destructures the existential drawing and reuses its vertex map and arc function. Its edge hypotheses are preserved because B ≤ A. The generic finite maximality child remains the main existence argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_subgraph_mono__p2m_b4d9d994_9c3d_480d_8aaa_85ca7382f67c_a1
    {V : Type} [Fintype V] [LinearOrder V] (B A : SimpleGraph V)
    (hBA : B ≤ A) (hA : HasPlanarDrawingOn A) : HasPlanarDrawingOn B := by
  sorry
