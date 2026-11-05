-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_certificate_edge_bound__p2m_4a8418ba_23c0_49b2_b768_f1b389811726_a4
-- name    : WilliamsonShmoys.face_certificate_edge_bound__p2m_4a8418ba_23c0_49b2_b768_f1b389811726_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:21:22.718021+00:00
-- url     : https://prove2.me/theorems/5cb1e131-54f8-4579-b09b-7ea425fe4806
-- title:
--   Face data implies the planar edge bound
-- statement:
--   Use the minimum face lengths to show three times the face count is at most twice the edge count. Combine this inequality with Euler’s equation and the edge-incidence sum to derive the stated edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_PlanarFaceCertificate__p2m_4a8418ba_23c0_49b2_b768_f1b389811726_a4

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.face_certificate_edge_bound__p2m_4a8418ba_23c0_49b2_b768_f1b389811726_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hfaces : WilliamsonShmoys.PlanarFaceCertificate__p2m_4a8418ba_23c0_49b2_b768_f1b389811726_a4 G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
