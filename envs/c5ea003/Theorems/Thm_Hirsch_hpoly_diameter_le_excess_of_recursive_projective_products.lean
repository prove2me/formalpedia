-- Prove2me | Theorems.Thm_Hirsch_hpoly_diameter_le_excess_of_recursive_projective_products
-- name    : Hirsch.hpoly_diameter_le_excess_of_recursive_projective_products
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-12T18:48:26.340851+00:00
-- url     : https://prove2.me/theorems/4afd7668-51a9-4a5e-a991-2a02c53b9e1c
-- title:
--   Recursive positive projective product certificates give the Hirsch row-excess bound
-- statement:
--   Let $P$ be described by $n$ real linear inequalities in $\mathbb R^d$.
--   Suppose it has a finite recursive geometric certificate built from the following operations.
--   A leaf is a bounded H-polyhedron with at most three excess describing rows.
--   An affine step transports a certificate through an affine equivalence without
--   changing the dimension or number of rows. At a split, an invertible linear
--   coordinate map and a partition of all rows identify a source with a Cartesian
--   product of at least two positive-dimensional certified factors. Each factor's
--   row count is at least its dimension. A positive projective map
--   $x\mapsto x/(1+c\cdot x)$ then sends this source onto the parent with sheared
--   rows $a_i+b_i c$; both forward and inverse denominators are required positive
--   on their full feasible sets. Different nodes may use different charts.
--
--   Then the ordinary-edge graph diameter of $P$ is at most $n-d$.
--   Product costs add and chart/affine transport preserves them, so the sum of leaf
--   excesses is exactly the parent excess. There is no restriction on total excess
--   or tree depth beyond the existence of the finite certificate.
--
--   This is a sufficient criterion. It does not assert that arbitrary polytopes
--   admit such trees, or that chart discovery is efficient. The separate exact
--   rational search is not part of this Lean theorem. Natural subtraction and
--   stationary walk steps follow the Hirsch model's padded diameter convention.
-- source:
--   Derived geometric certificate criterion; https://github.com/jjoshua2/prove2me-work/blob/fcbb02425dececaa9a8f7abd90c341ae99dbafac/research/RECURSIVE_PROJECTIVE_DISCOVERY_2026-09-12.md sections 1-3; classical projective invariance and product graph additivity are reused, not claimed novel.

import Mathlib
import Definitions.Def_Hirsch_recursive_projective_products
open Set Hirsch
open scoped RealInnerProductSpace

theorem Hirsch.hpoly_diameter_le_excess_of_recursive_projective_products {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (cert : HirschRecursiveProducts.ProductTree a b) : DiamLE (Hpoly a b) (n-d) := by sorry
