-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_89a3e2c0_b2b3_4ebc_a282_9a392a489cfc_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_89a3e2c0_b2b3_4ebc_a282_9a392a489cfc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:05:35.393316+00:00
-- url     : https://prove2.me/theorems/77901df4-aad7-410f-861f-76a2bd150be4
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strict drawable supergraph on the same vertices has exactly 3|V|−6 edges. A proof can derive connectedness and triangular faces from maximality, then apply Euler's formula and count face-edge incidences. This is the topological graph-theory core remaining in the reduction; it is not proved here.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_89a3e2c0_b2b3_4ebc_a282_9a392a489cfc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K <= L → WilliamsonShmoys.HasPlanarDrawingOn L → L <= K) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    3 * Fintype.card V = K.edgeFinset.card + 6 := by
  sorry
