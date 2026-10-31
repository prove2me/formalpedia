-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_a5f3545b_9213_4099_bf3a_a8a2e64023e0_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a5f3545b_9213_4099_bf3a_a8a2e64023e0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:49:07.508328+00:00
-- url     : https://prove2.me/theorems/63527105-a6ae-4611-ae89-0a92bfc94b6e
-- title:
--   Extend a planar drawing to an inclusion-maximal planar supergraph
-- statement:
--   Every graph with a planar drawing on a finite vertex type of size at least three has a planar supergraph on that same vertex type that is inclusion-maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a5f3545b_9213_4099_bf3a_a8a2e64023e0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : LE.le 3 (Fintype.card V))
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ T' : SimpleGraph V,
      LE.le T T' ∧ WilliamsonShmoys.HasPlanarDrawingOn T' ∧
      ∀ U : SimpleGraph V,
        LE.le T' U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T' := by sorry
