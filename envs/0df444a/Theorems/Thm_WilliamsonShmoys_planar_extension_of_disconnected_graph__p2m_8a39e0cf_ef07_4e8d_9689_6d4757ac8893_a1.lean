-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_of_disconnected_graph__p2m_8a39e0cf_ef07_4e8d_9689_6d4757ac8893_a1
-- name    : WilliamsonShmoys.planar_extension_of_disconnected_graph__p2m_8a39e0cf_ef07_4e8d_9689_6d4757ac8893_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:53:19.349204+00:00
-- url     : https://prove2.me/theorems/820a0dbc-c2b9-49d9-bf22-c9c2683d46a8
-- title:
--   Drawable strict extension of a disconnected graph
-- statement:
--   Every disconnected drawable graph on a finite linearly ordered vertex type with at least three vertices has a drawable strict supergraph on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_extension_of_disconnected_graph__p2m_8a39e0cf_ef07_4e8d_9689_6d4757ac8893_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) (hdis : ¬ K.Connected) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ ¬ L ≤ K := by sorry
