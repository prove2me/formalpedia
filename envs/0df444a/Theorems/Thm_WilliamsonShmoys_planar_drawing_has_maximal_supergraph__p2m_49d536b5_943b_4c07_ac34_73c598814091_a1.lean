-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph__p2m_49d536b5_943b_4c07_ac34_73c598814091_a1
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_49d536b5_943b_4c07_ac34_73c598814091_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:42:55.093926+00:00
-- url     : https://prove2.me/theorems/e8f37492-b876-4cc8-a661-6a339843396f
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has an inclusion-maximal drawable supergraph on the same vertices. There is no lower bound on the number of vertices; the given drawing itself ensures the candidate family is nonempty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph__p2m_49d536b5_943b_4c07_ac34_73c598814091_a1 {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hDraw : HasPlanarDrawingOn S) : ∃ T : SimpleGraph V, S ≤ T ∧ HasPlanarDrawingOn T ∧ ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U ≤ T := by sorry
