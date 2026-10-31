-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_a5f3545b_9213_4099_bf3a_a8a2e64023e0_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_a5f3545b_9213_4099_bf3a_a8a2e64023e0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:49:09.641268+00:00
-- url     : https://prove2.me/theorems/48e95b75-4adb-4d69-aa9e-831db1e4a1fa
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   A planar graph on a finite vertex type with at least three vertices has exactly `3|V|−6` edges if it has no strictly larger planar supergraph on that vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_a5f3545b_9213_4099_bf3a_a8a2e64023e0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hV : LE.le 3 (Fintype.card V))
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V,
      LE.le T U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
