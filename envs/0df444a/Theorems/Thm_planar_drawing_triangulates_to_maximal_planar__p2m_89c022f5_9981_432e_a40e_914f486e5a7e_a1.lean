-- Prove2me | Theorems.Thm_planar_drawing_triangulates_to_maximal_planar__p2m_89c022f5_9981_432e_a40e_914f486e5a7e_a1
-- name    : planar_drawing_triangulates_to_maximal_planar__p2m_89c022f5_9981_432e_a40e_914f486e5a7e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:25:28.041128+00:00
-- url     : https://prove2.me/theorems/c678df30-9cd8-4fa5-9888-0e5b50f2f715
-- title:
--   Triangulate a finite drawn simple graph
-- statement:
--   Every crossing-free drawing of a finite simple graph on at least three vertices can be extended, without adding vertices, to a crossing-free simple graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem planar_drawing_triangulates_to_maximal_planar__p2m_89c022f5_9981_432e_a40e_914f486e5a7e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 <= Fintype.card V) :
    ∃ (K' : SimpleGraph V) (dK' : DecidableRel K'.Adj),
      K ≤ K' ∧ WilliamsonShmoys.HasPlanarDrawingOn K' ∧
        (letI : DecidableRel K'.Adj := dK';
          K'.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
