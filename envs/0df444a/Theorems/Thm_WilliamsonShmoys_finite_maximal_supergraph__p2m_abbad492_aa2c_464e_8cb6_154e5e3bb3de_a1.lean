-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph__p2m_abbad492_aa2c_464e_8cb6_154e5e3bb3de_a1
-- name    : WilliamsonShmoys.finite_maximal_supergraph__p2m_abbad492_aa2c_464e_8cb6_154e5e3bb3de_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:10:58.658975+00:00
-- url     : https://prove2.me/theorems/d53236a8-1ece-4c70-9480-5c27d6fba8c0
-- title:
--   Finite maximal supergraph for a graph property
-- statement:
--   For any property of simple graphs on a finite vertex type, if H has that property, then H has a property-preserving supergraph that is inclusion-maximal among graphs with the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_maximal_supergraph__p2m_abbad492_aa2c_464e_8cb6_154e5e3bb3de_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V)
    (hP : P H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ P K ∧
      (∀ L : SimpleGraph V, K ≤ L → P L → L = K) := by sorry
