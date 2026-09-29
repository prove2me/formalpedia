-- Prove2me | Definitions.Def_Tropical_SATB_TropicalTensor
-- name    : Tropical_SATB_TropicalTensor
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:34.939702+00:00
-- url     : https://prove2.me/theorems/ffc5b6d8-4b98-4494-a4de-1b1054c51793
-- title:
--   Aether Catalog definitions — Tropical_SATB_TropicalTensor
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.SATB.TropicalTensor`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/SATB/TropicalTensor.lean by skeleton subtraction
import Mathlib

/-!
# Tropical Tensor Products and Finite Minimization

This module formalizes the core tropical (min-plus) algebra theorems for finite
product-space optimization:

1. **Product-space minimization** (`tropMin_prod`): The minimum of a function
   over a product `α × β` equals the iterated minimum `min_a min_b f(a,b)`.

2. **Tropical tensor additive theorem** (`tropMin_tropTensor`): For independent
   cost functions `f : α → ℝ` and `g : β → ℝ`, the minimum of their tropical
   tensor product `(a,b) ↦ f(a) + g(b)` equals `min f + min g`.

These are the finite exactness theorems behind Bellman elimination and
factorized energy minimization in tropical algebra.
-/

open Finset BigOperators

noncomputable section

/-- The tropical minimum of a real-valued function over a finite nonempty type.
    This is `inf` in the min-plus semiring. -/
def tropMin {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty f

/-- The tropical tensor product of two cost functions: pointwise addition. -/
def tropTensor {α β : Type*} (f : α → ℝ) (g : β → ℝ) : α × β → ℝ
  | (a, b) => f a + g b

variable {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]



/-
The minimum is attained: there exists `a` with `f a = tropMin f`.
-/

/-
**Theorem A: Product-space minimization.**
    The minimum over a product type equals the iterated minimum.
    This is the formal core of variable elimination in dynamic programming.
-/

/-
**Theorem B: Tropical tensor additive theorem.**
    For independent costs, `min_{a,b} (f(a) + g(b)) = min_a f(a) + min_b g(b)`.
-/

/-
There exists an optimal pair for any function on a product space.
-/

/-
There exists an optimal pair for a tropical tensor product.
-/

end


