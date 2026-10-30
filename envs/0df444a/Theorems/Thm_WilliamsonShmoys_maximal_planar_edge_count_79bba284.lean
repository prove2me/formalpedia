-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_79bba284
-- name    : WilliamsonShmoys.maximal_planar_edge_count_79bba284
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:19:56.41767+00:00
-- url     : https://prove2.me/theorems/44ee6346-c5c8-4937-ab77-ca51e02cb099
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A graph maximal under edge inclusion among graphs satisfying the supplied drawing predicate has exactly 3|V|−6 edges when |V|≥3. This removes the planar counting step from the parent. A proof route is to establish connectedness and triangular faces from maximality, apply Euler’s formula, and count each edge twice in face boundaries. The lower bound on |V| is essential to this triangulation conclusion, including the three-vertex case; formalizing the face structure for the given continuous-arc drawing predicate is the remaining core work.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_79bba284
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet ⊆ L.edgeSet) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
