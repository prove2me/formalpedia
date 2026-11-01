-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_a9c9dbb0_74a5_4e80_aeeb_6c6cfc8d46c4_a2
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a9c9dbb0_74a5_4e80_aeeb_6c6cfc8d46c4_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:25:23.222256+00:00
-- url     : https://prove2.me/theorems/c3b679a7-5abb-4fff-8dba-61888269c901
-- title:
--   Maximal drawable supergraph on the same vertices
-- statement:
--   Every finite graph with a crossing-free drawing has a drawable supergraph on the same vertices that is maximal among drawable supergraphs and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a9c9dbb0_74a5_4e80_aeeb_6c6cfc8d46c4_a2 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : (letI : DecidableRel L.Adj := Classical.decRel L.Adj; ∃ H : SimpleGraph V, L ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) ∧ (letI : DecidableRel H.Adj := Classical.decRel H.Adj; L.edgeFinset.card ≤ H.edgeFinset.card)) := by sorry
