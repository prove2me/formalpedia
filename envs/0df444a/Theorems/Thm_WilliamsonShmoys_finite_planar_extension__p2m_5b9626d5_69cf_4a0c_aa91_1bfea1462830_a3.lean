-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_extension__p2m_5b9626d5_69cf_4a0c_aa91_1bfea1462830_a3
-- name    : WilliamsonShmoys.finite_planar_extension__p2m_5b9626d5_69cf_4a0c_aa91_1bfea1462830_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T10:04:11.671954+00:00
-- url     : https://prove2.me/theorems/a2cbfef5-5bdd-4b7e-95ad-544626f6de95
-- title:
--   Iterate planar edge insertions to connect a finite graph
-- statement:
--   Given at least three vertices and a drawing-preserving edge-insertion rule for unreachable pairs, finitely many insertions produce a connected planar supergraph. The vertex-count hypothesis excludes the empty-type boundary case for graph connectedness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.finite_planar_extension__p2m_5b9626d5_69cf_4a0c_aa91_1bfea1462830_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hInsert : ∀ (G : SimpleGraph V), HasPlanarDrawingOn G →
      ∀ u v : V, ¬ G.Reachable u v →
        HasPlanarDrawingOn (G ⊔ SimpleGraph.edge u v)) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ N.Connected ∧ HasPlanarDrawingOn N := by sorry
