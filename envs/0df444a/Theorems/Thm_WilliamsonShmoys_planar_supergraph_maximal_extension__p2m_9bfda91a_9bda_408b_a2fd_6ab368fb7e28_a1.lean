-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_9bfda91a_9bda_408b_a2fd_6ab368fb7e28_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_9bfda91a_9bda_408b_a2fd_6ab368fb7e28_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:24:16.55978+00:00
-- url     : https://prove2.me/theorems/e2fe7145-1332-437c-98e8-1da8e1e565cf
-- title:
--   Finite maximal drawable supergraph extension
-- statement:
--   Every drawable finite graph on the given vertex type is contained in a drawable supergraph that has no strictly larger drawable supergraph on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_9bfda91a_9bda_408b_a2fd_6ab368fb7e28_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V, L.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      (∀ J : SimpleGraph V, K.edgeSet ⊆ J.edgeSet →
        HasPlanarDrawingOn J → J.edgeSet ⊆ K.edgeSet) := by sorry
