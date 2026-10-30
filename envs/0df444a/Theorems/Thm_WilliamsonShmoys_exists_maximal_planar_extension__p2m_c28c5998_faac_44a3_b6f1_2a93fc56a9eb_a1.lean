-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_c28c5998_faac_44a3_b6f1_2a93fc56a9eb_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_extension__p2m_c28c5998_faac_44a3_b6f1_2a93fc56a9eb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:51:26.42952+00:00
-- url     : https://prove2.me/theorems/8cd16ded-735f-4df7-8b84-93c58f4228da
-- title:
--   Existence of an edge-maximal planar extension
-- statement:
--   Every finite graph with a planar drawing has a planar supergraph on the same vertices that cannot be enlarged to a strictly larger planar graph. The hypothesis of at least three vertices is preserved to match the parent, though the finite maximization argument itself does not need it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_extension__p2m_c28c5998_faac_44a3_b6f1_2a93fc56a9eb_a1
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V, H ≤ J ∧ HasPlanarDrawingOn J ∧
      ∀ K : SimpleGraph V, J ≤ K → HasPlanarDrawingOn K → K = J := by
  sorry
