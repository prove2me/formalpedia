-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_5ca561e0_6863_43fe_aa41_85fb9a3351ed_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_5ca561e0_6863_43fe_aa41_85fb9a3351ed_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:26:34.598898+00:00
-- url     : https://prove2.me/theorems/93fb4221-4029-4870-92af-deed270da66d
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every graph with a drawing has a drawable supergraph on the same vertex type that is inclusion-maximal among drawable graphs. The finite maximization argument applies because there are finitely many simple graphs on the fixed finite vertex type and the family is nonempty (it contains the original graph). The child preserves the exact drawing predicate and states maximality against all drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_5ca561e0_6863_43fe_aa41_85fb9a3351ed_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    letI : forall K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    exists K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K /\ J <= K /\
      forall L : SimpleGraph V,
        K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L = K := by sorry
