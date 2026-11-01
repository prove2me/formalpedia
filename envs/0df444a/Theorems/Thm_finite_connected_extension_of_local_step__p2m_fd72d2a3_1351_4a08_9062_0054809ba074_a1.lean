-- Prove2me | Theorems.Thm_finite_connected_extension_of_local_step__p2m_fd72d2a3_1351_4a08_9062_0054809ba074_a1
-- name    : finite_connected_extension_of_local_step__p2m_fd72d2a3_1351_4a08_9062_0054809ba074_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:44:51.201203+00:00
-- url     : https://prove2.me/theorems/5e22ecc2-fcd1-4580-86fc-2603fce53c32
-- title:
--   Finite connected extension under a local joining step
-- statement:
--   For a finite vertex type, any graph predicate that contains K and satisfies the stated local joining condition has a connected supergraph of K satisfying that predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_connected_extension_of_local_step__p2m_fd72d2a3_1351_4a08_9062_0054809ba074_a1
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K)
    (hstep : ∀ (G : SimpleGraph V), K ≤ G → P G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
        ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ P H := by sorry
