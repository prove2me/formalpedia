-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_34ce151f_05d3_497c_a88f_b630e2f0d090_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_34ce151f_05d3_497c_a88f_b630e2f0d090_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:10:49.60785+00:00
-- url     : https://prove2.me/theorems/94af2c89-5b24-46b0-b9ee-d61ad09ab620
-- title:
--   Planar graphs admit a triangulated planar supergraph
-- statement:
--   Every finite simple graph with at least three vertices that has a crossing-free drawing on the given vertex type is contained in a planar supergraph on that same type with exactly 3|V|−6 edges. This includes disconnected graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_34ce151f_05d3_497c_a88f_b630e2f0d090_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hn : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (letI : DecidableRel L.Adj := Classical.decRel _;
       L.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
