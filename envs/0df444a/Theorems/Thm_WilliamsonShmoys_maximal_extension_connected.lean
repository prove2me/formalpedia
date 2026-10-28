-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_extension_connected
-- name    : WilliamsonShmoys.maximal_extension_connected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:29:34.817729+00:00
-- url     : https://prove2.me/theorems/f71ff2df-bfb2-460b-b0ed-147bf97f1524
-- title:
--   A maximal graph under bridge extensions is connected
-- statement:
--   If every disconnected graph satisfying P has a P-preserving supergraph with an edge between previously disconnected vertices, then a maximal P-preserving supergraph is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_extension_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P H)
    (hmax : ∀ J : SimpleGraph V, H ≤ J → P J → J = H)
    (bridge_extension : ∀ (J : SimpleGraph V),
      P J →
      ¬ (∀ u v : V, Nonempty (J.Walk u v)) →
      ∃ L : SimpleGraph V,
        J ≤ L ∧ P L ∧
        ∃ u v : V, ¬ Nonempty (J.Walk u v) ∧ L.Adj u v) :
    ∀ u v : V, Nonempty (H.Walk u v) := by sorry
