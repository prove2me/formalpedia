-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarAugmentation_edgeCount__p2m_6ad3e488_df98_4029_b402_def6549b4337_a1
-- name    : WilliamsonShmoys.planarAugmentation_edgeCount__p2m_6ad3e488_df98_4029_b402_def6549b4337_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:12:39.152305+00:00
-- url     : https://prove2.me/theorems/a840099d-4605-4d5d-aa63-effaab21667c
-- title:
--   Triangulating a finite planar graph without adding vertices
-- statement:
--   Every finite simply drawn planar graph on at least three vertices has a planar supergraph on the same vertices whose faces are triangular and whose edge count is 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarAugmentation_edgeCount__p2m_6ad3e488_df98_4029_b402_def6549b4337_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : HasPlanarDrawingOn K)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      HasPlanarDrawingOn L ∧
      (letI : DecidableRel K.Adj := dK
       letI : DecidableRel L.Adj := dL
       K.edgeFinset ⊆ L.edgeFinset) ∧
      (letI : DecidableRel L.Adj := dL
       L.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
