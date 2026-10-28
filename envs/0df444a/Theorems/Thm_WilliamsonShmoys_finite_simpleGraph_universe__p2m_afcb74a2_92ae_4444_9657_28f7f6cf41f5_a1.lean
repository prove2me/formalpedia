-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_universe__p2m_afcb74a2_92ae_4444_9657_28f7f6cf41f5_a1
-- name    : WilliamsonShmoys.finite_simpleGraph_universe__p2m_afcb74a2_92ae_4444_9657_28f7f6cf41f5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:33:55.454024+00:00
-- url     : https://prove2.me/theorems/104317e0-9f99-4744-977b-bf05542c5b03
-- title:
--   Simple graphs on a finite vertex type form a finite set
-- statement:
--   For a finite vertex type, there are only finitely many simple graphs on that type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Basic
set_option autoImplicit false

theorem WilliamsonShmoys.finite_simpleGraph_universe__p2m_afcb74a2_92ae_4444_9657_28f7f6cf41f5_a1
    {V : Type} [Fintype V] :
    (Set.univ : Set (SimpleGraph V)).Finite := by sorry
