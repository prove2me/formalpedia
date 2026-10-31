-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_2bf11b69_7074_453d_b4a4_93e188db5490_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal__p2m_2bf11b69_7074_453d_b4a4_93e188db5490_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:06:46.87744+00:00
-- url     : https://prove2.me/theorems/10e5fa50-ae85-4d68-b666-509a03938328
-- title:
--   Existence of an inclusion-maximal planar supergraph
-- statement:
--   Every finite planar graph on this vertex type has an inclusion-maximal planar supergraph on the same vertices. Maximality is among graphs admitting the specified drawing and containing the chosen graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_maximal__p2m_2bf11b69_7074_453d_b4a4_93e188db5490_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V) : ∃ T : SimpleGraph V, HasPlanarDrawingOn T ∧ H ≤ T ∧ ∀ K : SimpleGraph V, HasPlanarDrawingOn K → T ≤ K → K ≤ T := by sorry
