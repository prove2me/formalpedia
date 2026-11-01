-- Prove2me | Theorems.Thm_exists_maximal_superset_on_finite_type__p2m_d8eb9faa_7b6a_47f8_9dee_d4b2e8065d3d_a1
-- name    : exists_maximal_superset_on_finite_type__p2m_d8eb9faa_7b6a_47f8_9dee_d4b2e8065d3d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:30:36.600227+00:00
-- url     : https://prove2.me/theorems/d0cc2cac-35cc-4a64-9dcf-6596e31e9633
-- title:
--   Maximal accepted extension on a finite type
-- statement:
--   In a finite type whose elements are injectively represented by sets, every element satisfying P has a P-satisfying extension that is maximal under represented-set inclusion. Apply it with graphs as α, edge sets as the representation, and drawable graphs as P.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem exists_maximal_superset_on_finite_type__p2m_d8eb9faa_7b6a_47f8_9dee_d4b2e8065d3d_a1
    {α β : Type} [Fintype α]
    (edge : α → Set β)
    (hedge : Function.Injective edge)
    (P : α → Prop)
    (A : α)
    (hA : P A) :
    ∃ B : α,
      edge A ⊆ edge B ∧
      P B ∧
      ∀ C : α, edge B ⊆ edge C → P C → edge C = edge B := by sorry
