-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_4d6b09f4_cc64_4c42_8df1_4b93fc74bb58_a2
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_4d6b09f4_cc64_4c42_8df1_4b93fc74bb58_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:24:05.753193+00:00
-- url     : https://prove2.me/theorems/9d0adaf1-1fed-4091-9064-35996a6ee115
-- title:
--   Existence of an inclusion-maximal drawable extension
-- statement:
--   Every drawable finite simple graph on a finite linearly ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs under edge inclusion. This removes the finite maximal-extension argument from the parent. A proof route is to maximize edge-set cardinality among drawable supergraphs of `U`, a finite nonempty family. The statement also covers vertex types with fewer than three elements, provided `U` is drawable.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_4d6b09f4_cc64_4c42_8df1_4b93fc74bb58_a2 {V : Type} [Fintype V] [LinearOrder V] (U : SimpleGraph V) (hU : WilliamsonShmoys.HasPlanarDrawingOn U) : ∃ K : SimpleGraph V, U ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
