-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simple_graph_type__p2m_7421bb86_5406_4559_80b0_0937bd98493b_a2
-- name    : WilliamsonShmoys.finite_simple_graph_type__p2m_7421bb86_5406_4559_80b0_0937bd98493b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:43:34.870196+00:00
-- url     : https://prove2.me/theorems/e83ba9aa-efef-4d76-a1cc-c843eee2fd6b
-- title:
--   Finiteness of simple graphs on a finite vertex type
-- statement:
--   The type of simple graphs on a finite vertex type is finite. This supplies the finiteness hypothesis needed to apply the abstract maximal-extension result to graphs. A proof route encodes each graph by its set of edges, a subset of the finite type of unordered vertex pairs; this also covers an empty vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_simple_graph_type__p2m_7421bb86_5406_4559_80b0_0937bd98493b_a2 {V : Type} [Fintype V] : Finite (SimpleGraph V) := by sorry
