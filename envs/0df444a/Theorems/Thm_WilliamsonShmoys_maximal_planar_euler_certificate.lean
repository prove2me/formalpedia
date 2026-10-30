-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_certificate
-- name    : WilliamsonShmoys.maximal_planar_euler_certificate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:04:25.525226+00:00
-- url     : https://prove2.me/theorems/d89decc8-ddf1-4756-aeec-b7be0dd2ca86
-- title:
--   Euler and triangular incidence equations for maximal planar drawings
-- statement:
--   For a maximal planar drawing on at least three vertices, construct a natural face count satisfying Euler’s equation and the triangular face-edge incidence equation. This isolates the topological and maximality argument needed by the parent. A proof route is to construct a finite planar embedding from the supplied arcs, establish that maximality forces triangular faces, and count incidences. The drawing predicate itself provides the arcs but no faces; this child contains the remaining substantial core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_euler_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by sorry
