-- Prove2me | Theorems.Thm_SubgroupCount_card_subgroup_card_eq_prime
-- name    : SubgroupCount.card_subgroup_card_eq_prime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:59:13.336869+00:00
-- url     : https://prove2.me/theorems/e373b3bf-b378-447a-8b1e-ed584ef1c1c8
-- title:
--   The `p + 1` lines.
-- statement:
--   **The `p + 1` lines.**  A group of order `p²` and exponent `p` has exactly `p + 1` subgroups
--   of order `p`.
--
--   ```lean
--   theorem SubgroupCount.card_subgroup_card_eq_prime(hp : p.Prime) (hcard : Nat.card G = p ^ 2)
--       (hexp : ∀ x : G, x ^ p = 1) :
--       Nat.card {K : Subgroup G // Nat.card K = p} = p + 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/SubgroupCountFiniteAbelian.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/SubgroupCountFiniteAbelian.lean#L238

-- Thm stub generated from Algebra/SubgroupCountFiniteAbelian.lean
import Mathlib
import Definitions.Def_Algebra_SubgroupCountFiniteAbelian
/-
# Counting the subgroups of a finite group

This file settles the group-theoretic half of target 1 of the previous research cycle of the
conditional Hilbert class field thread.  By
`HilbertClassFieldDescent.card_intermediateField_eq_card_subgroup`, the number of intermediate
fields of a Hilbert class field `H/K` is the number of subgroups of the class group, so the
arithmetic question "how many intermediate fields?" becomes the group-theoretic question
"how many subgroups?".  The previous cycle answered it for elementary abelian class groups
`(ℤ/p)^r` (the Galois `p`-binomial count).  Here we prove:

* `Subgroup.eq_prod_of_coprime`, `subgroupProdOrderIsoOfCoprime`,
  `card_subgroup_prod_of_coprime` : **multiplicativity**.  If `Nat.card G` and `Nat.card H` are
  coprime then every subgroup of `G × H` is a product of subgroups, the subgroup lattice of
  `G × H` is the product of the two subgroup lattices, and
  `#Subgroup (G × H) = #Subgroup G * #Subgroup H`.  (No commutativity is needed.)
* `card_subgroup_cyclic` : a finite **cyclic** group of order `n` has exactly `d(n)` subgroups,
  `d` the number-of-divisors function.
* `card_subgroup_of_sq_prime_card` : a group of order `p²` of exponent `p` (`p` prime) has
  exactly `p + 3` subgroups: `⊥`, `⊤` and the `p + 1` "lines".
* `card_subgroup_zmod_four`, `card_subgroup_kleinFour`, `card_subgroup_ne_of_order_four` :
  the falsifiable contrast announced in the previous cycle — `ℤ/4` has `3` subgroups while
  `(ℤ/2)²` has `5`, so **the number of intermediate fields of the Hilbert class field is not a
  function of the class number alone**.

Everything is stated for multiplicative groups; the additive models `ZMod n` are reached through
`Multiplicative`.
-/


open Subgroup

open SubgroupCount


/-! ## Multiplicativity over a coprime product -/


variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]










/-! ## Cyclic groups: the divisor count -/


variable {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]






/-! ## Elementary abelian groups of rank two -/


variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem SubgroupCount.card_subgroup_card_eq_prime(hp : p.Prime) (hcard : Nat.card G = p ^ 2)
    (hexp : ∀ x : G, x ^ p = 1) :
    Nat.card {K : Subgroup G // Nat.card K = p} = p + 1 := by sorry
