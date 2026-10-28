-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_connected_extension_of_step
-- name    : WilliamsonShmoys.finite_connected_extension_of_step
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:34:50.325897+00:00
-- url     : https://prove2.me/theorems/05db1d4c-ca0a-439f-8574-1d52ca6dd0b3
-- title:
--   Iterate strict finite graph extensions to connectivity
-- statement:
--   For a finite vertex type, if every disconnected extension of a base graph satisfying an invariant `P` can be extended again while preserving `P` and joining previously unreachable vertices, then there is a `P`-preserving connected extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_connected_extension_of_step
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (T : SimpleGraph V)
    (hT : P T)
    (hstep : ∀ (G : SimpleGraph V), T ≤ G → P G → ¬ G.Connected →
      ∃ H : SimpleGraph V,
        G ≤ H ∧ P H ∧ ∃ u v, ¬ G.Reachable u v ∧ H.Adj u v) :
    ∃ S : SimpleGraph V, T ≤ S ∧ P S ∧ S.Connected := by sorry
