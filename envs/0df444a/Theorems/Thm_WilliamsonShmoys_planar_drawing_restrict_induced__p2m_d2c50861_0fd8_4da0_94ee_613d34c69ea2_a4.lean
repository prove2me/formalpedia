-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_restrict_induced__p2m_d2c50861_0fd8_4da0_94ee_613d34c69ea2_a4
-- name    : WilliamsonShmoys.planar_drawing_restrict_induced__p2m_d2c50861_0fd8_4da0_94ee_613d34c69ea2_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:13:32.49853+00:00
-- url     : https://prove2.me/theorems/54dcafe2-42f0-4dd8-9f0b-c3fe11f591b2
-- title:
--   Restriction of a planar drawing to an induced subgraph
-- statement:
--   Restrict the vertex placement and edge arcs witnessing the drawing of G to vertices in s. The subtype order preserves edge orientation, and the injectivity, endpoint, interior-vertex, continuity, and noncrossing conditions are inherited. Prove this by unpacking the drawing witnesses and composing them with the subtype coercion. This removes drawing restriction from the parent argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_restrict_induced__p2m_d2c50861_0fd8_4da0_94ee_613d34c69ea2_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (s : Set V)
    [Fintype {x // x ∈ s}] [LinearOrder {x // x ∈ s}]:
    HasPlanarDrawingOn (G.induce s) := by sorry
