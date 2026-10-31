-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_aef33245_cc08_4f0b_a789_a34216bab8c3_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_aef33245_cc08_4f0b_a789_a34216bab8c3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:22:04.274283+00:00
-- url     : https://prove2.me/theorems/aab4ced3-2cb3-4a94-814b-7026a53a954f
-- title:
--   An inclusion-maximal drawable supergraph exists
-- statement:
--   A drawable graph on a finite fixed vertex type has a drawable supergraph that is inclusion-maximal among drawable supergraphs on that same type. The cardinality lower bound is retained to match the parent hypotheses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_aef33245_cc08_4f0b_a789_a34216bab8c3_a1
    {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N := by sorry
