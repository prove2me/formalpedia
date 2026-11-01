-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_98d2ce50_16ca_4db3_bebc_b1953e5d6a1b_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_98d2ce50_16ca_4db3_bebc_b1953e5d6a1b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:47:18.947203+00:00
-- url     : https://prove2.me/theorems/eba63f99-4b89-43c7-9979-04802f4e758b
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable strict supergraph on the same vertex set has exactly 3n−6 edges. The independent proof route is to derive connectedness and triangular faces from maximality, and then count vertices, edges, and faces using Euler’s formula. This isolates the substantive planar-topology and counting argument from the parent. The exact crossing-free arc conditions must be shown to support those planar-map facts; the threshold n≥3 is retained because it is essential to the edge-count formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_98d2ce50_16ca_4db3_bebc_b1953e5d6a1b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : HasPlanarDrawingOn U)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ W : SimpleGraph V, U ≤ W → HasPlanarDrawingOn W → W = U) :
    (letI : DecidableRel U.Adj := Classical.decRel U.Adj
     U.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
