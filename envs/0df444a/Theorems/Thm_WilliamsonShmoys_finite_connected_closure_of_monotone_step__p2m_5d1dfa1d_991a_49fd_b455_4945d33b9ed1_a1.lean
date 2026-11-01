-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_connected_closure_of_monotone_step__p2m_5d1dfa1d_991a_49fd_b455_4945d33b9ed1_a1
-- name    : WilliamsonShmoys.finite_connected_closure_of_monotone_step__p2m_5d1dfa1d_991a_49fd_b455_4945d33b9ed1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:28:31.533261+00:00
-- url     : https://prove2.me/theorems/d09a4cfd-adba-43aa-a539-0dbb6da2696f
-- title:
--   Iterate monotone reachability steps to connectedness
-- statement:
--   On a finite vertex type, any graph property preserved by a one-step augmentation that makes a formerly unreachable pair reachable can be extended to a connected supergraph while retaining the property. The finite measure is the number of reachable ordered vertex pairs: graph inclusion preserves reachability, and every step strictly increases that number. This separates the finite iteration argument from the geometric construction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_connected_closure_of_monotone_step__p2m_5d1dfa1d_991a_49fd_b455_4945d33b9ed1_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hstep : ∀ G : SimpleGraph V, P G → ¬ G.Connected →
      ∃ K : SimpleGraph V,
        G ≤ K ∧ P K ∧
        ∃ u v : V, ¬ G.Reachable u v ∧ K.Reachable u v) :
    ∀ G : SimpleGraph V, P G →
      ∃ K : SimpleGraph V, G ≤ K ∧ K.Connected ∧ P K := by sorry
