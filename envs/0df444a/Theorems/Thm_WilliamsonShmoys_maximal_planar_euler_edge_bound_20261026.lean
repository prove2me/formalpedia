-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_edge_bound_20261026
-- name    : WilliamsonShmoys.maximal_planar_euler_edge_bound_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:13:52.090702+00:00
-- url     : https://prove2.me/theorems/ed53988f-6337-4ff2-a3f0-b70ff66e45c2
-- title:
--   Euler edge bound for a maximal planar drawing
-- statement:
--   A graph maximal among planar supergraphs on the same finite vertex type, with at least three vertices, has at most 3|V|−6 edges. The hypotheses include the supplied crossing-free drawing predicate and preserve the vertex-count boundary required by the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_euler_edge_bound_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hHmax : ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
