-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_connected__p2m_94f9dee3_44c3_4c29_a91e_073301a1623a_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_connected__p2m_94f9dee3_44c3_4c29_a91e_073301a1623a_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:26:10.976234+00:00
-- url     : https://prove2.me/theorems/4d39bfdd-3b15-4c53-aa35-0f292c6309dd
-- title:
--   An edge-maximal drawable graph is connected
-- statement:
--   A drawable graph on at least three vertices that has no drawable strict edge supergraph is connected. A proof must construct an arc in the complement joining distinct components while retaining the drawing conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.maximal_planar_drawing_connected__p2m_94f9dee3_44c3_4c29_a91e_073301a1623a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V) [DecidableRel L.Adj],
      K.edgeFinset ⊆ L.edgeFinset →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeFinset ⊆ K.edgeFinset) :
    K.Connected := by sorry
