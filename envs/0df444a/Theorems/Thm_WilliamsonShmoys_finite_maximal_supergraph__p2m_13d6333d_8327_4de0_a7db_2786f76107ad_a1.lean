-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph__p2m_13d6333d_8327_4de0_a7db_2786f76107ad_a1
-- name    : WilliamsonShmoys.finite_maximal_supergraph__p2m_13d6333d_8327_4de0_a7db_2786f76107ad_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:07:17.527305+00:00
-- url     : https://prove2.me/theorems/b15aa635-5dcf-46ed-8e16-f3f8ba72d59c
-- title:
--   Finite maximal supergraph principle
-- statement:
--   For any property of graphs on a finite linearly ordered vertex type, if Q satisfies the property, there is a supergraph of Q satisfying it that is maximal under edge inclusion among graphs satisfying the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_supergraph__p2m_13d6333d_8327_4de0_a7db_2786f76107ad_a1 {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (P : SimpleGraph V -> Prop) (hP : P Q) : Exists fun R : SimpleGraph V => And (Set.Subset Q.edgeSet R.edgeSet) (And (P R) (forall S : SimpleGraph V, Set.Subset R.edgeSet S.edgeSet -> P S -> Set.Subset S.edgeSet R.edgeSet)) := by sorry
