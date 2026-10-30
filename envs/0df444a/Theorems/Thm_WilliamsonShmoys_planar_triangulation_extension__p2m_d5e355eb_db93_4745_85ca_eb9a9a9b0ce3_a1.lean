-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_d5e355eb_db93_4745_85ca_eb9a9a9b0ce3_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_d5e355eb_db93_4745_85ca_eb9a9a9b0ce3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:11:13.595231+00:00
-- url     : https://prove2.me/theorems/8e19dc79-980c-4b90-a9e5-d9bf409450af
-- title:
--   Extend a finite planar graph to a maximal planar graph with the triangulation edge count
-- statement:
--   Every finite drawable simple graph on an ordered vertex type with at least three vertices has a drawable supergraph on that same vertex type whose edge count is 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_d5e355eb_db93_4745_85ca_eb9a9a9b0ce3_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
