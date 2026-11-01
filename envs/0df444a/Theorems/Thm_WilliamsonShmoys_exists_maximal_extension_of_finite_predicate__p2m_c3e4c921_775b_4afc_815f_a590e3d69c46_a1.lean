-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_of_finite_predicate__p2m_c3e4c921_775b_4afc_815f_a590e3d69c46_a1
-- name    : WilliamsonShmoys.exists_maximal_extension_of_finite_predicate__p2m_c3e4c921_775b_4afc_815f_a590e3d69c46_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:56:58.692876+00:00
-- url     : https://prove2.me/theorems/7a87286a-5f91-41f5-b308-99c5664b45e2
-- title:
--   Finite maximal extension for a graph predicate
-- statement:
--   For any predicate on graphs over a finite vertex type, every graph satisfying the predicate is contained in a predicate-satisfying graph that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_extension_of_finite_predicate__p2m_c3e4c921_775b_4afc_815f_a590e3d69c46_a1
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (M : SimpleGraph V) (hM : P M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ P N ∧
      ∀ K : SimpleGraph V, N ≤ K → P K → K = N := by sorry
