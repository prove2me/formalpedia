-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_c0cea038_5072_4638_ab37_572b27cc73e9_a1
-- name    : WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_c0cea038_5072_4638_ab37_572b27cc73e9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T07:04:13.280989+00:00
-- url     : https://prove2.me/theorems/d06a677f-9861-40c2-9d53-0b6f71b189f9
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertex type that is maximal under edge inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_c0cea038_5072_4638_ab37_572b27cc73e9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := by sorry
