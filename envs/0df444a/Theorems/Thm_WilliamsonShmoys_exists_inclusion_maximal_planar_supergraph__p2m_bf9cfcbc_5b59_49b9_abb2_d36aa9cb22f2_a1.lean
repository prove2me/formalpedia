-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_bf9cfcbc_5b59_49b9_abb2_d36aa9cb22f2_a1
-- name    : WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_bf9cfcbc_5b59_49b9_abb2_d36aa9cb22f2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:20:10.049417+00:00
-- url     : https://prove2.me/theorems/8fa7b5e9-9ae2-4561-bc62-ceb5c7ac1a09
-- title:
--   Existence of an inclusion-maximal planar supergraph on the same vertices
-- statement:
--   Every finitely drawn planar graph has a supergraph on the same vertices that is inclusion-maximal among graphs on those vertices admitting such a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_bf9cfcbc_5b59_49b9_abb2_d36aa9cb22f2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V, M ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H := by sorry
