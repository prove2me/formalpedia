-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_44d3f95a_e4af_4a94_b096_ba30239a3f07
-- name    : WilliamsonShmoys.edgeSet_ncard_mono_44d3f95a_e4af_4a94_b096_ba30239a3f07
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:10:49.15252+00:00
-- url     : https://prove2.me/theorems/79d61159-2553-41d0-ab95-39ec8e978e00
-- title:
--   Monotonicity of finite edge-set cardinality
-- statement:
--   If one simple graph is a subgraph of another on the same finite vertices, its edge-set cardinality is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_mono_44d3f95a_e4af_4a94_b096_ba30239a3f07
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  sorry
