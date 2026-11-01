-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_exists__p2m_74da5e6a_674d_4f79_986e_ea1a1f3184a0_a1
-- name    : WilliamsonShmoys.planar_maximal_extension_exists__p2m_74da5e6a_674d_4f79_986e_ea1a1f3184a0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:19:46.263203+00:00
-- url     : https://prove2.me/theorems/f3019428-8b1e-423c-898a-892c51cc6294
-- title:
--   Existence of an inclusion-maximal drawable extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that has no strictly larger drawable supergraph on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_extension_exists__p2m_74da5e6a_674d_4f79_986e_ea1a1f3184a0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Exists fun M : SimpleGraph V =>
      (forall {u v : V}, L.Adj u v -> M.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      (forall N : SimpleGraph V,
        (forall {u v : V}, M.Adj u v -> N.Adj u v) ->
        WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) := by sorry
