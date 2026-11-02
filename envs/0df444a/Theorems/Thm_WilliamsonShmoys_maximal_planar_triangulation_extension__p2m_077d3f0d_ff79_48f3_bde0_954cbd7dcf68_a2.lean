-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_extension__p2m_077d3f0d_ff79_48f3_bde0_954cbd7dcf68_a2
-- name    : WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_077d3f0d_ff79_48f3_bde0_954cbd7dcf68_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:50:13.791178+00:00
-- url     : https://prove2.me/theorems/3461d3ef-e829-4302-a17d-0f8fc9f6195e
-- title:
--   Planar completion to a triangulation edge count
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3n − 6 edges. This supplies the triangulated completion used by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_077d3f0d_ff79_48f3_bde0_954cbd7dcf68_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    letI : forall K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    exists J : SimpleGraph V, And (HasPlanarDrawingOn J)
      (And (H <= J) (J.edgeFinset.card = 3 * Fintype.card V - 6)) := by sorry
