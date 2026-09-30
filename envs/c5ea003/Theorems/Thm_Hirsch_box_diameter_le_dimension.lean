-- Prove2me | Theorems.Thm_Hirsch_box_diameter_le_dimension
-- name    : Hirsch.box_diameter_le_dimension
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T06:21:36.77789+00:00
-- url     : https://prove2.me/theorems/97c8bc54-2060-46d4-927b-6abbcbfb8436
-- title:
--   An axis-aligned box has graph diameter at most the number of coordinates
-- statement:
--   **Diameter of an axis-aligned box.** Let $\mathrm{cap}$ assign a real capacity to each of $d$ coordinates, and let
--
--   $$
--   B=\bigl\{x\in\mathbb{R}^d\ \big|\ 0\le x_k\le\mathrm{cap}_k\text{ for every coordinate }k\bigr\}.
--   $$
--
--   The vertex-edge graph of $B$ has padded combinatorial diameter at most $d$: any two extreme points are joined by a walk of at most $d$ edges (stationary steps allowed). If some capacity is negative the box is empty and the statement is vacuous. Zero-width coordinates and $d=0$ are included.
--
--   Vertices of a nonempty box have each coordinate at a bound $0$ or $\mathrm{cap}_k$. The walk that, at step $t$, copies the target's $t$-th coordinate (and leaves the others unchanged) is a genuine edge whenever those two bound values differ, because the other coordinates remain extreme in their intervals. This is the product-of-intervals theorem $\mathrm{diam}(I_1\times\cdots\times I_d)\le d$, and it is not the unrestricted polynomial Hirsch conjecture. It is complementary to the existing one-balance box-slice theorem, which additionally imposes $\sum x_k=\mathrm{total}$.
-- source:
--   Standard fact: the 1-skeleton of a product of intervals is a box graph of diameter equal to the number of nondegenerate factors. Complementary to Hirsch.box_slice_diameter_le_dimension (one linear balance equation). No literature-priority claim.

import Mathlib
import Definitions.Def_Hirsch_model
open Set Hirsch

theorem Hirsch.box_diameter_le_dimension (d : ℕ) (cap : Fin d → ℝ) :
    DiamLE {x : Fin d → ℝ | ∀ k, 0 ≤ x k ∧ x k ≤ cap k} d := by sorry
