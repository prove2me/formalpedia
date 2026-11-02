-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_58a4bbec_9b1c_4062_8fb0_876ba124b0f6_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_58a4bbec_9b1c_4062_8fb0_876ba124b0f6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:00:04.640893+00:00
-- url     : https://prove2.me/theorems/bde7bab7-9900-4674-96b7-2eea7887c7cc
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every connected finite graph with a planar drawing and at least three vertices is contained, on the same vertex set, in a planar graph maximal under adding edges while preserving the drawing property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_58a4bbec_9b1c_4062_8fb0_876ba124b0f6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : HasPlanarDrawingOn N)
    (hconn : N.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ u v : V, N.Adj u v → H.Adj u v) ∧
      HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        (∀ u v : V, H.Adj u v → K.Adj u v) →
        HasPlanarDrawingOn K → K = H) := by sorry
