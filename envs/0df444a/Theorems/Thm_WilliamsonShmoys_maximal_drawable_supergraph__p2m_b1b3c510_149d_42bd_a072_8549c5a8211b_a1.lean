-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph__p2m_b1b3c510_149d_42bd_a072_8549c5a8211b_a1
-- name    : WilliamsonShmoys.maximal_drawable_supergraph__p2m_b1b3c510_149d_42bd_a072_8549c5a8211b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:59:56.57671+00:00
-- url     : https://prove2.me/theorems/82c89845-7cfb-4e98-a37d-e1c5831c9413
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type is contained in a drawable supergraph on the same vertices that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_supergraph__p2m_b1b3c510_149d_42bd_a072_8549c5a8211b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L := by sorry
