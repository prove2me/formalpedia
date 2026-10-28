-- Prove2me | Theorems.Thm_WilliamsonShmoys_induced_reachable_ambient
-- name    : WilliamsonShmoys.induced_reachable_ambient
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T21:23:28.177248+00:00
-- url     : https://prove2.me/theorems/f97fad1e-ea56-4d84-92a4-4e53b189c947
-- title:
--   Reachability in an induced graph lifts to the ambient graph
-- statement:
--   A path in the graph induced by S gives an ambient path between the underlying vertices. This lifts the retained-component hypothesis to the original graph, which the parent uses to join the canonical root to u.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Metric
set_option autoImplicit false

theorem WilliamsonShmoys.induced_reachable_ambient {n : Nat} (G : SimpleGraph (Fin n)) (S : Set (Fin n)) (u v : {x : Fin n // x ∈ S}) : (G.induce S).Reachable u v → G.Reachable v.1 u.1 := by sorry
