-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_certificate_from_edge_bounds_41afc169_9eb4_4682_8d03_09ec36ef1b9a
-- name    : WilliamsonShmoys.face_certificate_from_edge_bounds_41afc169_9eb4_4682_8d03_09ec36ef1b9a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:18:56.076406+00:00
-- url     : https://prove2.me/theorems/7e9111f1-0f43-49c0-b179-cd9f373ead1a
-- title:
--   Build face certificate data from edge bounds
-- statement:
--   For a finite simple graph on at least three vertices with between n−1 and 3n−6 edges, construct list-based boundary data satisfying the supplied certificate fields by distributing the two orientations of every edge among m+2−n lists.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarFaceCertificate

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.face_certificate_from_edge_bounds_41afc169_9eb4_4682_8d03_09ec36ef1b9a
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hmin : Fintype.card V - 1 ≤ L.edgeSet.ncard)
    (hmax : L.edgeSet.ncard ≤ 3 * Fintype.card V - 6) :
    Nonempty (WilliamsonShmoys.PlanarFaceCertificate L) := by sorry
