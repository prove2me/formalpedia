-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_extension_by_pair_connections_cert38ffb807
-- name    : WilliamsonShmoys.finite_extension_by_pair_connections_cert38ffb807
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:35:08.877274+00:00
-- url     : https://prove2.me/theorems/3020e216-5a09-4d58-8c01-dfb26de678d3
-- title:
--   Finite iteration of pair-connection extensions
-- statement:
--   For a finite nonempty vertex type, an invariant-preserving extension operation that connects any chosen pair of disconnected vertices yields an invariant-preserving connected supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_extension_by_pair_connections_cert38ffb807
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (P : SimpleGraph V → Prop) (hPK : P K)
    (hstep : ∀ (G : SimpleGraph V), K ≤ G → P G →
      ∀ u v : V, u ≠ v → ¬ Relation.ReflTransGen G.Adj u v →
        ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧ Relation.ReflTransGen H.Adj u v) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ P H := by
  sorry
