-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_supergraph__p2m_1d9e4996_f1da_4af7_951a_5adb0b1eb381_a1
-- name    : WilliamsonShmoys.planar_drawable_maximal_supergraph__p2m_1d9e4996_f1da_4af7_951a_5adb0b1eb381_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T09:17:05.953097+00:00
-- url     : https://prove2.me/theorems/d8aa7015-594b-44f0-b66b-a7cd4c31cad4
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every finite drawable graph has an inclusion-maximal drawable supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawable_maximal_supergraph__p2m_1d9e4996_f1da_4af7_951a_5adb0b1eb381_a1 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) : ∃ P : SimpleGraph V, Set.Subset N.edgeSet P.edgeSet ∧ HasPlanarDrawingOn P ∧ ∀ Q : SimpleGraph V, Set.Subset P.edgeSet Q.edgeSet → HasPlanarDrawingOn Q → Set.Subset Q.edgeSet P.edgeSet := by sorry
