-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph__p2m_57a6043d_0c29_4d4d_8b4a_350055d97afc_a1
-- name    : WilliamsonShmoys.finite_maximal_supergraph__p2m_57a6043d_0c29_4d4d_8b4a_350055d97afc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:13:18.349224+00:00
-- url     : https://prove2.me/theorems/817f3096-b030-457a-9798-8dcb06521640
-- title:
--   Finite extremal supergraph principle
-- statement:
--   For any predicate on simple graphs over a finite ordered vertex type, if K satisfies the predicate, there is a supergraph H that still satisfies it, has at least as many edges, and has no proper supergraph satisfying the predicate and containing K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_supergraph__p2m_57a6043d_0c29_4d4d_8b4a_350055d97afc_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (dK : DecidableRel K.Adj) (P : SimpleGraph V → Prop) (hK : P K) : ∃ H : SimpleGraph V, ∃ dH : DecidableRel H.Adj, K ≤ H ∧ P H ∧ Nat.le K.edgeFinset.card H.edgeFinset.card ∧ ∀ J : SimpleGraph V, K ≤ J → P J → H ≤ J → J = H := by sorry
