-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_maximal__p2m_9b3efef9_88d6_4457_a3f3_6508d18ac1de_a2
-- name    : WilliamsonShmoys_finite_planar_supergraph_maximal__p2m_9b3efef9_88d6_4457_a3f3_6508d18ac1de_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:06:00.922164+00:00
-- url     : https://prove2.me/theorems/1841e8f3-3dc0-4413-8d65-8f642645b455
-- title:
--   Finite maximal planar supergraph
-- statement:
--   Every finite graph with a planar drawing has a planar supergraph on the same vertex type that is maximal among planar supergraphs under subgraph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_finite_planar_supergraph_maximal__p2m_9b3efef9_88d6_4457_a3f3_6508d18ac1de_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hGplanar : WilliamsonShmoys.HasPlanarDrawingOn G) : Exists fun K : SimpleGraph V => And (LE.le G K) (And (WilliamsonShmoys.HasPlanarDrawingOn K) (∀ L : SimpleGraph V, LE.le K L → WilliamsonShmoys.HasPlanarDrawingOn L → LE.le L K)) := by sorry
