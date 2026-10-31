-- Prove2me | Theorems.Thm_finite_maximal_extension_for_downward_closed_graph_property__p2m_8c20c3de_e0e6_4d41_88fb_de4af60b0786_a1
-- name    : finite_maximal_extension_for_downward_closed_graph_property__p2m_8c20c3de_e0e6_4d41_88fb_de4af60b0786_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:33:20.771735+00:00
-- url     : https://prove2.me/theorems/77b0e74d-6b01-4882-938e-d874f1442f21
-- title:
--   Finite maximal extension for a downward-closed graph property
-- statement:
--   For a finite vertex type, every graph satisfying a downward-closed property is contained in a graph maximal under edge inclusion among graphs satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_maximal_extension_for_downward_closed_graph_property__p2m_8c20c3de_e0e6_4d41_88fb_de4af60b0786_a1
    {V : Type} [Fintype V] (P : SimpleGraph V → Prop)
    (hdown : ∀ {G K : SimpleGraph V}, G ≤ K → P K → P G)
    (H : SimpleGraph V) (hH : P H) :
    ∃ T : SimpleGraph V, H ≤ T ∧ P T ∧
      ∀ T' : SimpleGraph V, T ≤ T' → P T' → T' = T := by sorry
