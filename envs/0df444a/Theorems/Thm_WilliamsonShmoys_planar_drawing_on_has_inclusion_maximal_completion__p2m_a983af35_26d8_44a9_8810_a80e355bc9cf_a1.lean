-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_on_has_inclusion_maximal_completion__p2m_a983af35_26d8_44a9_8810_a80e355bc9cf_a1
-- name    : WilliamsonShmoys.planar_drawing_on_has_inclusion_maximal_completion__p2m_a983af35_26d8_44a9_8810_a80e355bc9cf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:11:56.161348+00:00
-- url     : https://prove2.me/theorems/0785a672-0d6a-4bee-973a-0294d6448cb4
-- title:
--   Existence of an inclusion-maximal drawable completion
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertices that has no strictly larger drawable supergraph. This removes the finite selection and maximality step from the target; prove it by maximizing edge count over the finite set of supergraphs that contain T and have a drawing. The candidate set is nonempty because it contains T.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_on_has_inclusion_maximal_completion__p2m_a983af35_26d8_44a9_8810_a80e355bc9cf_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hT : HasPlanarDrawingOn T) : Exists fun U : SimpleGraph V => T ≤ U ∧ HasPlanarDrawingOn U ∧ ∀ W : SimpleGraph V, U ≤ W → HasPlanarDrawingOn W → W ≤ U := by
  sorry
