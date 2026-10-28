-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_0d153890
-- name    : WilliamsonShmoys.exists_maximal_planar_extension_0d153890
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:14:34.181511+00:00
-- url     : https://prove2.me/theorems/cc0b2481-9b0c-4d58-866e-ecea565517fe
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable graph with no drawable strict supergraph on that same vertex type. A proof maximizes the edge count among the finitely many simple graphs containing the original graph and having a planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_extension_0d153890
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = H := by sorry
