-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_ef0860d4_4cfe_4ed1_9f37_9a24872db6ea_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_ef0860d4_4cfe_4ed1_9f37_9a24872db6ea_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:23:24.888257+00:00
-- url     : https://prove2.me/theorems/53e9b636-bd68-45e0-a03f-9baafaf2e758
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph that has no strictly larger drawable supergraph on the same vertex set. The proof route is to maximize edge count among the finite family of drawable supergraphs of T, then use edge inclusion and equal edge count to establish maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_ef0860d4_4cfe_4ed1_9f37_9a24872db6ea_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      T ≤ U ∧
      ∀ W : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn W → U ≤ W → W ≤ U := by sorry
