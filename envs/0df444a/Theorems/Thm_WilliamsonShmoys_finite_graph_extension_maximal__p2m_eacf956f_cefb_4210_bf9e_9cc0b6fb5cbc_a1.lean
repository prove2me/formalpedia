-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_extension_maximal__p2m_eacf956f_cefb_4210_bf9e_9cc0b6fb5cbc_a1
-- name    : WilliamsonShmoys.finite_graph_extension_maximal__p2m_eacf956f_cefb_4210_bf9e_9cc0b6fb5cbc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:36:55.286695+00:00
-- url     : https://prove2.me/theorems/c73a1eef-abb4-46aa-80da-3fb553ccc4a8
-- title:
--   Finite maximal extension with a monotone measure
-- statement:
--   In a finite vertex type, any graph K satisfying P has a supergraph H satisfying P that is maximal under inclusion among P-supergraphs of K, and whose inclusion-monotone natural-valued measure is at least that of K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.finite_graph_extension_maximal__p2m_eacf956f_cefb_4210_bf9e_9cc0b6fb5cbc_a1
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (P : SimpleGraph V → Prop) (μ : SimpleGraph V → Nat)
    (hK : P K)
    (hmono : ∀ G J : SimpleGraph V, G ≤ J → μ G ≤ μ J) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ P H ∧
      (∀ J : SimpleGraph V, H ≤ J → P J → J = H) ∧
      μ K ≤ μ H := by sorry
