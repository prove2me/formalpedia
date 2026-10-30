-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_same_vertex_set__p2m_b07b2cea_077c_4214_a610_9ab8bd281015_a1
-- name    : WilliamsonShmoys.planar_maximal_extension_same_vertex_set__p2m_b07b2cea_077c_4214_a610_9ab8bd281015_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:25:53.876463+00:00
-- url     : https://prove2.me/theorems/4f4a8988-3a83-4c97-870a-3e268ffa4b52
-- title:
--   Maximal planar extension on a fixed vertex set
-- statement:
--   Every planar simple graph on a finite ordered vertex type with at least three vertices is contained in a planar graph on the same vertices that has no strictly larger planar supergraph on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_extension_same_vertex_set__p2m_b07b2cea_077c_4214_a610_9ab8bd281015_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    exists L : SimpleGraph V,
      K <= L /\ WilliamsonShmoys.HasPlanarDrawingOn L /\
      (forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) := by sorry
