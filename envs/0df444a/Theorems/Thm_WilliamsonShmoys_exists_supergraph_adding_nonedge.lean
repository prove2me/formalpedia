-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_supergraph_adding_nonedge
-- name    : WilliamsonShmoys.exists_supergraph_adding_nonedge
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-26T06:29:36.505506+00:00
-- url     : https://prove2.me/theorems/60cfaae7-d070-46a9-9fec-26056bc4f5ce
-- title:
--   Add a missing pair as the only new edge
-- statement:
--   For a nonadjacent pair u,v, there is a simple graph extending G in which u and v are adjacent and every edge is either an old edge or that pair.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_supergraph_adding_nonedge
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V) (hNotAdj : ¬ G.Adj u v) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Adj u v ∧
        ∀ x y, H.Adj x y →
          G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by sorry
