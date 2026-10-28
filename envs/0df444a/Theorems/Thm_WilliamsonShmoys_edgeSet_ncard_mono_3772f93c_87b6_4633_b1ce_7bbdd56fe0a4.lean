-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4
-- name    : WilliamsonShmoys.edgeSet_ncard_mono_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:18:51.366997+00:00
-- url     : https://prove2.me/theorems/a279c666-13fb-47cf-8847-ffd95059fd98
-- title:
--   Monotonicity of finite edge-set cardinality
-- statement:
--   Show that a subgraph on the same finite vertex type has no more edges than its supergraph, by deriving inclusion of edge sets and applying finite-set cardinality monotonicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.edgeSet_ncard_mono_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4
    {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V) (hKH : K ≤ H) :
    K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
