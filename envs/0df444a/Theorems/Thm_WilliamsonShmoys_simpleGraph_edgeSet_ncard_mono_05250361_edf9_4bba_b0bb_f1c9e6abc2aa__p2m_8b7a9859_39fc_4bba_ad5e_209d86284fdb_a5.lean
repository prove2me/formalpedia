-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleGraph_edgeSet_ncard_mono_05250361_edf9_4bba_b0bb_f1c9e6abc2aa__p2m_8b7a9859_39fc_4bba_ad5e_209d86284fdb_a5
-- name    : WilliamsonShmoys.simpleGraph_edgeSet_ncard_mono_05250361_edf9_4bba_b0bb_f1c9e6abc2aa__p2m_8b7a9859_39fc_4bba_ad5e_209d86284fdb_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T01:42:17.601687+00:00
-- url     : https://prove2.me/theorems/868d2853-58cc-435d-bdc4-38fa6cf2e7e2
-- title:
--   Monotonicity of finite simple graph edge count
-- statement:
--   If every edge of one finite graph is also an edge of another on the same vertices, then its finite edge-set cardinality is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
set_option autoImplicit false

theorem WilliamsonShmoys.simpleGraph_edgeSet_ncard_mono_05250361_edf9_4bba_b0bb_f1c9e6abc2aa__p2m_8b7a9859_39fc_4bba_ad5e_209d86284fdb_a5
    {V : Type} [Fintype V]
    (M Q : SimpleGraph V)
    (hMQ : ∀ {u v : V}, M.Adj u v → Q.Adj u v) :
    (M.edgeSet.ncard : Int) ≤ (Q.edgeSet.ncard : Int) := by sorry
