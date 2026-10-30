-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_minimal_connected_extension__p2m_9960b19b_62d8_4924_9bd4_14f246de67e1_a3
-- name    : WilliamsonShmoys.exists_minimal_connected_extension__p2m_9960b19b_62d8_4924_9bd4_14f246de67e1_a3
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-29T23:58:04.820481+00:00
-- url     : https://prove2.me/theorems/af495ada-8c1f-484d-a693-c45034ff536b
-- title:
--   Finite graph has a minimal connected extension
-- statement:
--   Every finite simple graph is contained in a connected supergraph such that deleting any added edge disconnects its endpoints. The empty vertex type is covered because connectivity and the endpoint condition are vacuous.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.exists_minimal_connected_extension__p2m_9960b19b_62d8_4924_9bd4_14f246de67e1_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) :
    ∃ H : SimpleGraph V, M ≤ H ∧ H.Connected ∧
      ∀ u v : V, H.Adj u v → ¬ M.Adj u v →
        ¬ (H.deleteEdges {s(u, v)}).Reachable u v := by sorry
