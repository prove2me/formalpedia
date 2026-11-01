-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulated_supergraph__p2m_40182049_fc6a_4cfb_9899_f86d953b2959_a5
-- name    : WilliamsonShmoys.exists_planar_triangulated_supergraph__p2m_40182049_fc6a_4cfb_9899_f86d953b2959_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:20:40.367848+00:00
-- url     : https://prove2.me/theorems/4e737f0c-cfdf-4405-baad-6e647949d837
-- title:
--   Drawable planar supergraph with maximal planar edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex set of size at least three has a drawable supergraph on the same vertex set with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.exists_planar_triangulated_supergraph__p2m_40182049_fc6a_4cfb_9899_f86d953b2959_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∃ (_ : DecidableRel K.Adj),
        K.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
