-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_connected
-- name    : WilliamsonShmoys.maximal_drawable_graph_connected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T03:50:34.778997+00:00
-- url     : https://prove2.me/theorems/af405077-1d40-42c1-bcd1-e732652b284e
-- title:
--   Connectivity of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that admits no drawable edge extension is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      Q ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M ≤ Q) :
    Q.Connected := by sorry
