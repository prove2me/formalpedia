-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_connected__p2m_986cca2a_af96_41ca_97f1_9fc97c42977c_a2
-- name    : WilliamsonShmoys.maximal_planar_extension_connected__p2m_986cca2a_af96_41ca_97f1_9fc97c42977c_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T07:11:55.585198+00:00
-- url     : https://prove2.me/theorems/e1e588d9-e5f4-4625-abb9-7285f0042a1e
-- title:
--   A maximal drawable extension is connected
-- statement:
--   If `H` is drawable and maximal among drawable supergraphs of `K` on the same finite vertex type, then `H` is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.maximal_planar_extension_connected__p2m_986cca2a_af96_41ca_97f1_9fc97c42977c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hKH : K ≤ H)
    (hmax : ∀ J : SimpleGraph V,
      K ≤ J →
      WilliamsonShmoys.HasPlanarDrawingOn J →
      H ≤ J → J = H) :
    H.Connected := by
  sorry
