-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_extension_maximal_property__p2m_73c85c29_4333_4692_baee_7210fe30cead_a2
-- name    : WilliamsonShmoys.finite_extension_maximal_property__p2m_73c85c29_4333_4692_baee_7210fe30cead_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:51:21.755567+00:00
-- url     : https://prove2.me/theorems/c71aecbc-486a-4dc7-bf57-ff12d30dbcea
-- title:
--   A nonempty finite family of graph extensions has a maximal member
-- statement:
--   For a finite vertex type, if some graph extending M satisfies P, then there is a P graph extending M with no strictly larger P graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.finite_extension_maximal_property__p2m_73c85c29_4333_4692_baee_7210fe30cead_a2
    {V : Type} [Fintype V]
    (M : SimpleGraph V)
    (P : SimpleGraph V -> Prop)
    (hP : exists G : SimpleGraph V, M <= G /\ P G) :
    exists N : SimpleGraph V,
      M <= N /\
      P N /\
      forall K : SimpleGraph V, N <= K -> P K -> K = N := by sorry
