-- Prove2me | Theorems.Thm_finite_predicate_maximal_supergraph__p2m_768c520d_0a53_42aa_bcb6_e73e3939ed8f_a2
-- name    : finite_predicate_maximal_supergraph__p2m_768c520d_0a53_42aa_bcb6_e73e3939ed8f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T20:34:43.301774+00:00
-- url     : https://prove2.me/theorems/038327fe-4daf-4028-a7aa-65aa49782279
-- title:
--   Finite maximal supergraph for a graph predicate
-- statement:
--   For a finite ordered vertex type, any graph satisfying a predicate has a predicate-satisfying supergraph that is maximal among predicate-satisfying supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_predicate_maximal_supergraph__p2m_768c520d_0a53_42aa_bcb6_e73e3939ed8f_a2 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : P G) : ∃ K : SimpleGraph V, P K ∧ Set.Subset G.edgeSet K.edgeSet ∧ (∀ H : SimpleGraph V, P H → Set.Subset K.edgeSet H.edgeSet → Set.Subset H.edgeSet K.edgeSet) := by sorry
