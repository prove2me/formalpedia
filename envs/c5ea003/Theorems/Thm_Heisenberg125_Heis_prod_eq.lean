-- Prove2me | Theorems.Thm_Heisenberg125_Heis_prod_eq
-- name    : Heisenberg125.Heis.prod_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:47:41.838439+00:00
-- url     : https://prove2.me/theorems/7458d7b5-e318-4523-9c38-62ba6d1b3975
-- title:
--   Product formula.
-- statement:
--   **Product formula.**  The product of a list of Heisenberg elements has
--   first two coordinates the (order independent) coordinate sums, and third
--   coordinate the sum of third coordinates plus the order-dependent cross sum
--   `Σ_{i<j} a_i b_j`.
--
--   ```lean
--   theorem Heisenberg125.Heis.prod_eq(L : List (Heis p)) :
--       L.prod = ⟨asum L, bsum L, csum L + crossSum L⟩ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/Heisenberg125/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/Heisenberg125/Basic.lean#L144

-- Thm stub generated from Algebra/Heisenberg125/Basic.lean
import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
/-
# The Heisenberg group `H_{p^3}` of exponent `p`, and product-one-free sequences

This file sets up the objects needed to study the *small Davenport constant*
`d(G)` (the maximal length of a product-one-free sequence over a finite group
`G`) for the exponent-`p` Heisenberg group

  `H_{p^3} = { (a,b,c) : a,b,c ∈ ZMod p }`,  `(a,b,c)(a',b',c') = (a+a', b+b', c+c'+a b')`,

which is the group of upper unitriangular `3 × 3` matrices over `ZMod p`.

Main contents:

* `Heis p` with its group structure, cardinality `p ^ 3`, commutator formula and
  (for odd `p`) exponent `p`.
* `Heis.crossSum` and the **product formula** `Heis.prod_eq`: the product of a
  list is `(Σ a, Σ b, Σ c + Σ_{i<j} a_i b_j)`.  This is the bridge that turns the
  non-commutative product-one problem into additive combinatorics over
  `(ZMod p)^2`.
* `IsProductOne`, `ProductOneFree`, `smallDavenport` for an arbitrary group, and
  the general pigeonhole bound `d(G) ≤ |G| - 1`.
-/

open Heisenberg125

/-! ## The Heisenberg group -/


open Heis

variable {p : ℕ}

instance : Inv (Heis p) := ⟨fun g => ⟨-g.a, -g.b, -g.c + g.a * g.b⟩⟩









/-! ### Cardinality -/




/-! ## Products of lists -/

theorem Heisenberg125.Heis.prod_eq(L : List (Heis p)) :
    L.prod = ⟨asum L, bsum L, csum L + crossSum L⟩ := by sorry
