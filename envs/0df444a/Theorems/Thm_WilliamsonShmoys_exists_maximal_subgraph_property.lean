-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_subgraph_property
-- name    : WilliamsonShmoys.exists_maximal_subgraph_property
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:00:38.637522+00:00
-- url     : https://prove2.me/theorems/3f863111-6b3c-4aa7-9975-ff5fcb49a5e7
-- title:
--   A graph property on a finite vertex type has an inclusion-maximal member
-- statement:
--   Every nonempty property of simple graphs on a finite vertex type has a member that is maximal under subgraph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_subgraph_property
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hP : ∃ G : SimpleGraph V, P G) :
    ∃ L : SimpleGraph V, P L ∧
      ∀ M : SimpleGraph V, P M → L ≤ M → M = L := by sorry
