-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_71345845_0812_4936_9e60_f9671145c018_a2
-- name    : WilliamsonShmoys.exists_maximal_planar_extension__p2m_71345845_0812_4936_9e60_f9671145c018_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:14:39.053667+00:00
-- url     : https://prove2.me/theorems/3721485b-3cdc-4a3e-9978-b518aa3e9dbd
-- title:
--   Existence of an inclusion-maximal drawable extension
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type has a drawable supergraph on the same vertices that is maximal under graph inclusion among drawable graphs. A proof route is to maximize edge count over the finite set of drawable supergraphs of the input graph. This step applies even when the input graph is empty or disconnected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_extension__p2m_71345845_0812_4936_9e60_f9671145c018_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) :
    ∃ T : SimpleGraph V, L ≤ T ∧ HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U = T := by
  sorry
