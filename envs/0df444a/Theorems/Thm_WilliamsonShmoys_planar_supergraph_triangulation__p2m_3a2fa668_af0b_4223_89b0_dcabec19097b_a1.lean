-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation__p2m_3a2fa668_af0b_4223_89b0_dcabec19097b_a1
-- name    : WilliamsonShmoys.planar_supergraph_triangulation__p2m_3a2fa668_af0b_4223_89b0_dcabec19097b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:30:56.41678+00:00
-- url     : https://prove2.me/theorems/2313d792-5eb0-4345-85d6-32f091bb14d8
-- title:
--   Drawable triangulating supergraph on the same vertices
-- statement:
--   Every graph drawable in the given sense on at least three finite linearly ordered vertices has a drawable supergraph on the same vertex type with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_triangulation__p2m_3a2fa668_af0b_4223_89b0_dcabec19097b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
