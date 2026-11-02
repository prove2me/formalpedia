-- Prove2me | Theorems.Thm_finite_maximal_planar_property_extension__p2m_503a8d71_6799_480d_8f3e_33232e674c95_a1
-- name    : finite_maximal_planar_property_extension__p2m_503a8d71_6799_480d_8f3e_33232e674c95_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:40:11.833455+00:00
-- url     : https://prove2.me/theorems/4d73fc9a-4d3f-4feb-81ae-a00df8c50165
-- title:
--   Finite maximal extension for a graph property
-- statement:
--   For any property of simple graphs on a finite ordered vertex type, every graph satisfying that property has a property-satisfying supergraph that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem finite_maximal_planar_property_extension__p2m_503a8d71_6799_480d_8f3e_33232e674c95_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : P M) :
    ∃ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      P N ∧
      (letI : DecidableRel M.Adj := dM
       letI : DecidableRel N.Adj := dN
       M.edgeFinset ⊆ N.edgeFinset) ∧
      (∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
        P K →
        (letI : DecidableRel N.Adj := dN
         letI : DecidableRel K.Adj := dK
         N.edgeFinset ⊆ K.edgeFinset) →
        N = K) := by sorry
