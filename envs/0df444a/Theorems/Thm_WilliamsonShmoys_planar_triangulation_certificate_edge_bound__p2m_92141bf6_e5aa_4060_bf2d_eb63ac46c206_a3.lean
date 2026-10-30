-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_certificate_edge_bound__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3
-- name    : WilliamsonShmoys.planar_triangulation_certificate_edge_bound__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:43:19.916986+00:00
-- url     : https://prove2.me/theorems/3df5d745-28b9-40bd-a2a8-59b2557c5a2c
-- title:
--   Count edges from a planar triangulation certificate
-- statement:
--   The certificate’s supergraph inclusion, Euler equation, face-degree lower bounds, and face-edge incidence equation imply the edge bound for the original graph. The order hypothesis handles natural-number subtraction at the boundary.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_PlanarTriangulationCertificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_certificate_edge_bound__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3 {V : Type} [Fintype V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (c : WilliamsonShmoys.PlanarTriangulationCertificate__p2m_92141bf6_e5aa_4060_bf2d_eb63ac46c206_a3 H) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
