-- Prove2me | Theorems.Thm_planar_drawable_edge_upper_bound__p2m_d2caba73_4b7e_439a_8f09_ce231377a6dc_a2
-- name    : planar_drawable_edge_upper_bound__p2m_d2caba73_4b7e_439a_8f09_ce231377a6dc_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T13:01:11.995472+00:00
-- url     : https://prove2.me/theorems/89c022f5-9981-432e-a40e-914f486e5a7e
-- title:
--   Edge upper bound for a drawable simple graph
-- statement:
--   Every drawable simple graph with at least three vertices has at most 3|V|−6 edges. This child isolates the planar counting bound used by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem planar_drawable_edge_upper_bound__p2m_d2caba73_4b7e_439a_8f09_ce231377a6dc_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 <= Fintype.card V) :
    letI : DecidableRel K.Adj := dK
    K.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
