-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_ncard_mono_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671
-- name    : WilliamsonShmoys.edge_ncard_mono_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:21:04.761114+00:00
-- url     : https://prove2.me/theorems/3eaef34a-dcab-4c45-88d4-3b86ad6345e7
-- title:
--   Monotonicity of finite graph edge counts
-- statement:
--   For finite simple graphs on the same vertex type, graph inclusion implies monotonicity of the integer-cast edge-set cardinality. No vertex-count restriction is needed. Prove it by deriving edge-set inclusion, applying finite cardinality monotonicity, and casting the resulting natural-number inequality to integers. This supplies the parent’s final transfer step independently of planarity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_ncard_mono_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    (G.edgeSet.ncard : Int) ≤ (H.edgeSet.ncard : Int) := by sorry
