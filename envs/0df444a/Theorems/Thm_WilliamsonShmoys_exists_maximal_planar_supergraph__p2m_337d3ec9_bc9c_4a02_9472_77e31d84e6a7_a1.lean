-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_337d3ec9_bc9c_4a02_9472_77e31d84e6a7_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_337d3ec9_bc9c_4a02_9472_77e31d84e6a7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T22:54:10.52463+00:00
-- url     : https://prove2.me/theorems/11d28411-8f98-4345-999b-a4dbc94b8fe5
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable supergraph on the same vertices that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_337d3ec9_bc9c_4a02_9472_77e31d84e6a7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      (∀ x y, T.Adj x y → U.Adj x y) ∧
      HasPlanarDrawingOn U ∧
      ∀ W : SimpleGraph V,
        (∀ x y, U.Adj x y → W.Adj x y) →
        HasPlanarDrawingOn W → W = U := by sorry
