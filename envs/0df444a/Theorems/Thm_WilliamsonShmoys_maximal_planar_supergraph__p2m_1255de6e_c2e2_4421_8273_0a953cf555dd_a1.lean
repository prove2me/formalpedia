-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_1255de6e_c2e2_4421_8273_0a953cf555dd_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_1255de6e_c2e2_4421_8273_0a953cf555dd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:08:50.935971+00:00
-- url     : https://prove2.me/theorems/fe1a9c4f-5aad-4a32-a050-44f6e8cc3efe
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every finite planar graph on at least three vertices has a planar supergraph on the same vertex type that is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_1255de6e_c2e2_4421_8273_0a953cf555dd_a1 {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J ≤ H := by sorry
