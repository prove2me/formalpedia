-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_78a07d33_949e_45fc_983f_eb458ca767ac_a2
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_78a07d33_949e_45fc_983f_eb458ca767ac_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:14:49.847481+00:00
-- url     : https://prove2.me/theorems/5ca561e0-6863-43fe-aa41-85fb9a3351ed
-- title:
--   Triangulation extension of a finite planar drawing
-- statement:
--   Every finite graph with a crossing-free drawing on at least three vertices is a subgraph, on the same vertex set, of a drawable graph with exactly 3|V|−6 edges. This isolates the extension-to-triangulation and Euler-counting work; the parent handles maximality and transfers the count to J.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_78a07d33_949e_45fc_983f_eb458ca767ac_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hcard : 3 <= Fintype.card V) :
    letI : forall K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    exists K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K /\ J <= K /\
      K.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
