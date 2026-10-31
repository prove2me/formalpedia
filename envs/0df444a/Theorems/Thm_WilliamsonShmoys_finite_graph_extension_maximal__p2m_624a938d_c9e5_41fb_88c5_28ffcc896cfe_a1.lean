-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_extension_maximal__p2m_624a938d_c9e5_41fb_88c5_28ffcc896cfe_a1
-- name    : WilliamsonShmoys.finite_graph_extension_maximal__p2m_624a938d_c9e5_41fb_88c5_28ffcc896cfe_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:29:40.551697+00:00
-- url     : https://prove2.me/theorems/bbc501e7-b3ec-428e-99b9-e6dd0bd1255a
-- title:
--   Maximal extension in a finite family of simple graphs
-- statement:
--   For any predicate on simple graphs over a finite vertex type, if H satisfies the predicate, then H has a predicate-satisfying supergraph maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_graph_extension_maximal__p2m_624a938d_c9e5_41fb_88c5_28ffcc896cfe_a1 {V : Type} [Fintype V] (H : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P H) : ∃ T : SimpleGraph V, H ≤ T ∧ P T ∧ ∀ U : SimpleGraph V, T ≤ U → P U → U = T := by sorry
