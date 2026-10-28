-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_connected_supergraph_of_strict_extension
-- name    : WilliamsonShmoys.exists_connected_supergraph_of_strict_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:37:32.417852+00:00
-- url     : https://prove2.me/theorems/d511a59a-a2f0-439c-bf32-f5f12994a05c
-- title:
--   Finite strict extensions reach a connected graph
-- statement:
--   For a finite vertex type, if a graph has property P and each disconnected P-supergraph admits a strictly larger P-supergraph, then it has a connected P-supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_connected_supergraph_of_strict_extension
    {V : Type} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (P : SimpleGraph V → Prop) (hPK : P K)
    (hstep : ∀ G, K ≤ G → P G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G < H ∧ P H) :
    ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧ H.Connected := by sorry
