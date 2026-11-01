-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_on_same_vertices__p2m_06e45311_b4a8_47cf_99af_36dad6983f39_a1
-- name    : WilliamsonShmoys.maximal_planar_extension_on_same_vertices__p2m_06e45311_b4a8_47cf_99af_36dad6983f39_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:21:45.240599+00:00
-- url     : https://prove2.me/theorems/7762f2e5-af20-4909-9894-1de106545d78
-- title:
--   Finite maximal planar extension on the same vertices
-- statement:
--   Every drawn finite simple graph has a drawn edge-maximal supergraph on the same vertices, containing all original edges and therefore having at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension_on_same_vertices__p2m_06e45311_b4a8_47cf_99af_36dad6983f39_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧
      (∀ {u v : V}, K.Adj u v → H.Adj u v) ∧
      (∀ H' : SimpleGraph V,
        (∀ {u v : V}, H'.Adj u v → H.Adj u v) →
        HasPlanarDrawingOn H' → H' = H) ∧
      K.edgeFinset.card ≤ H.edgeFinset.card := by sorry
