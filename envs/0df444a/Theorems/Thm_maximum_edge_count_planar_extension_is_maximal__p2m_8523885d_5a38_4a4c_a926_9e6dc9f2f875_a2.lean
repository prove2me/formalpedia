-- Prove2me | Theorems.Thm_maximum_edge_count_planar_extension_is_maximal__p2m_8523885d_5a38_4a4c_a926_9e6dc9f2f875_a2
-- name    : maximum_edge_count_planar_extension_is_maximal__p2m_8523885d_5a38_4a4c_a926_9e6dc9f2f875_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:49:03.877125+00:00
-- url     : https://prove2.me/theorems/1b695860-cf62-435d-80fc-e9845ec6b02f
-- title:
--   A maximum-edge planar extension is inclusion-maximal
-- statement:
--   If H is a planar extension of G with maximum edge-set cardinality among planar extensions of G, then no planar graph can strictly contain H.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem maximum_edge_count_planar_extension_is_maximal__p2m_8523885d_5a38_4a4c_a926_9e6dc9f2f875_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hHDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, G ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ H.edgeSet.ncard) :
    ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
