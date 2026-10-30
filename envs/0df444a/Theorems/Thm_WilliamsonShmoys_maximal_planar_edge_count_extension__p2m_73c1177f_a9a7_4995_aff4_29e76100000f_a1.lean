-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_extension__p2m_73c1177f_a9a7_4995_aff4_29e76100000f_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_extension__p2m_73c1177f_a9a7_4995_aff4_29e76100000f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:19:59.422231+00:00
-- url     : https://prove2.me/theorems/316c89ef-5381-45bf-ad7e-e8d13020052b
-- title:
--   Planar extension reaches the maximal planar edge bound
-- statement:
--   Every finite planar graph on at least three vertices has a planar supergraph on the same vertex set whose edge count is at least 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_extension__p2m_73c1177f_a9a7_4995_aff4_29e76100000f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∃ (_ : DecidableRel L.Adj),
        3 * Fintype.card V - 6 ≤ L.edgeFinset.card := by sorry
