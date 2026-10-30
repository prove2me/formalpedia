-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_316c89ef_5381_45bf_ad7e_e8d13020052b_a2
-- name    : WilliamsonShmoys.planar_maximal_extension__p2m_316c89ef_5381_45bf_ad7e_e8d13020052b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:41:59.756579+00:00
-- url     : https://prove2.me/theorems/03e90475-cbaa-4d30-84cc-f87b4a621968
-- title:
--   Extend a finite planar graph to a maximal planar supergraph
-- statement:
--   Every finite planar graph on at least three vertices has a planar supergraph on the same vertex set that is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_extension__p2m_316c89ef_5381_45bf_ad7e_e8d13020052b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (∃ (_ : DecidableRel L.Adj),
        ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) := by sorry
