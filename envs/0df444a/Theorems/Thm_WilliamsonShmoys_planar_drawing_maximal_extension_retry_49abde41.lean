-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_retry_49abde41
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_retry_49abde41
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:57:51.301827+00:00
-- url     : https://prove2.me/theorems/4ba48782-8050-4953-a83c-5e99ae75d18e
-- title:
--   Existence of a maximal planar supergraph on the same vertices
-- statement:
--   Every finite graph with a crossing-free drawing has a supergraph on the same vertices that is maximal among planar supergraphs under edge inclusion. This removes the finite extension-existence step from the parent. The family is nonempty because it contains G and finite because there are finitely many simple graphs on V. Choose a member with maximum edge-set cardinality; a strict planar extension would have more edges, contradicting maximality of the chosen cardinality. This child does not require |V| ≥ 3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_retry_49abde41
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
