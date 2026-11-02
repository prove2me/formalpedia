-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_34c1d13a_c463_44f3_a4ff_eb6476f05c93_a2
-- name    : WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_34c1d13a_c463_44f3_a4ff_eb6476f05c93_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:54:37.71482+00:00
-- url     : https://prove2.me/theorems/75c86ecd-00c9-4da6-b3eb-332cdc8728f4
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on the given finite vertex type has a drawable supergraph that is inclusion-maximal among drawable supergraphs on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_34c1d13a_c463_44f3_a4ff_eb6476f05c93_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ T : SimpleGraph V, G ≤ T ∧ HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U = T := by sorry
