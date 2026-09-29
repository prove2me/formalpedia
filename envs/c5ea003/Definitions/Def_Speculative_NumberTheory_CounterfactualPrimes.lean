-- Prove2me | Definitions.Def_Speculative_NumberTheory_CounterfactualPrimes
-- name    : Speculative_NumberTheory_CounterfactualPrimes
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:33:23.455998+00:00
-- url     : https://prove2.me/theorems/c9f94fdd-0e00-464d-bd91-8d11dcd15c94
-- title:
--   Aether Catalog definitions — Speculative_NumberTheory_CounterfactualPrimes
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.NumberTheory.CounterfactualPrimes`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/NumberTheory/CounterfactualPrimes.lean by skeleton subtraction
import Mathlib

/-!
# Counterfactual Number Theory: What If Primes Were Random?

## Overview

We develop the theory of *generator sets* — arbitrary subsets S ⊆ ℕ used as
building blocks for multiplicative factorization — and determine which structural
properties of the primes are essential for unique factorization.

The central question: if we replace the primes with a random subset of ℕ having
the same asymptotic density (n / log n), which classical theorems survive?

**Answer**: Unique factorization collapses completely. We identify two independent
failure modes — *PMI violations* (products of generators being generators) and
*product collisions* (distinct pairs with equal products) — and prove that pairwise
multiplicative independence, while necessary, is strictly insufficient for unique
factorization. The primes avoid both failure modes thanks to their *irreducibility*
in (ℕ, ×), a structural property that random sets lack.

## Main Results

* `product_in_S_breaks_uf`: If S contains a, b, and a·b (all ≥ 2), then
  unique factorization over S fails.
* `uf_implies_pmi`: Unique factorization ⟹ pairwise multiplicative independence.
* `primes_pmi`: The primes satisfy PMI.
* `collision_breaks_uf`: Product collisions break unique factorization.
* `exists_pmi_with_collision`: PMI does not prevent collisions ({6, 10, 21, 35}).
* `pmi_strictly_weaker_than_uf`: PMI is strictly weaker than UF.

## Novel Concept: Product Collision

A *product collision* in S is a quadruple (a, b, c, d) ∈ S⁴ with a·b = c·d
but {a,b} ≠ {c,d} as multisets. This captures a deeper obstruction to unique
factorization invisible to PMI. The primes avoid collisions via irreducibility.
-/

namespace CounterfactualPrimes

/-- An S-factorization of n: a nonempty multiset of elements from S with product n.
    This generalizes prime factorization to arbitrary generator sets. -/
structure SFact (S : Set ℕ) (n : ℕ) where
  factors : Multiset ℕ
  mem_S : ∀ x ∈ factors, x ∈ S
  prod_eq : factors.prod = n
  card_pos : 0 < factors.card

/-- A set S has *unique factorization* if any two S-factorizations of the same
    number yield identical multisets of factors. -/
def HasUF (S : Set ℕ) : Prop :=
  ∀ n : ℕ, ∀ f g : SFact S n, f.factors = g.factors

/-- *Pairwise multiplicative independence* (PMI): no product of two elements
    of S (each ≥ 2) lies in S. This is the most basic necessary condition
    for unique factorization — it prevents "composite pseudo-primes." -/
def PMI (S : Set ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ S → b ∈ S → 2 ≤ a → 2 ≤ b → a * b ∉ S

/-- A *product collision* in S: four elements a, b, c, d ∈ S with a·b = c·d
    but {a,b} ≠ {c,d} as multisets. This is a novel obstruction concept that
    captures the failure of unique factorization beyond PMI violations.

    In classical number theory, the Fundamental Theorem of Arithmetic
    guarantees that primes have no product collisions. Random generator sets
    with density n/log(n) almost surely have abundant collisions. -/
structure ProductCollision (S : Set ℕ) where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  ha : a ∈ S
  hb : b ∈ S
  hc : c ∈ S
  hd : d ∈ S
  prod_eq : a * b = c * d
  distinct : (↑[a, b] : Multiset ℕ) ≠ ↑[c, d]

/-! ### Core Structural Theorems -/

/-
**Theorem (PMI Violation Breaks UF)**: If S contains elements a, b, and
    their product a·b (with a, b ≥ 2), then S does not have unique factorization.

    The number a·b admits two distinct S-factorizations: the singleton
    multiset {a·b} and the pair {a, b}. These differ in cardinality (1 vs 2).
-/


/-
**Theorem (Primes Have PMI)**: The set of prime numbers satisfies pairwise
    multiplicative independence. No product of two primes is itself prime.
-/

/-
**Theorem (Collisions Break UF)**: Any product collision in S witnesses
    failure of unique factorization.
-/

/-! ### Separation: PMI Does Not Imply UF -/

/-- The witness set for the separation theorem: {6, 10, 21, 35}. -/
private def witnessSet : Set ℕ := ({6, 10, 21, 35} : Set ℕ)

/-
The witness set satisfies PMI: no product of two elements is an element.
    Verified by checking all 16 products.
-/

/-- The witness set admits the product collision 6·35 = 10·21 = 210. -/
private def witnessSet_collision : ProductCollision witnessSet where
  a := 6
  b := 35
  c := 10
  d := 21
  ha := by simp [witnessSet]
  hb := by simp [witnessSet]
  hc := by simp [witnessSet]
  hd := by simp [witnessSet]
  prod_eq := by norm_num
  distinct := by decide



/-! ### Conjecture: Cramér Factorization Collapse

**Conjecture**: In the Cramér random model — where each integer n ≥ 2 is
included in S independently with probability 1/log(n) — unique factorization
fails almost surely.

More precisely: the expected number of product collisions (a,b,c,d) ∈ S⁴
with a·b = c·d ≤ N, {a,b} ≠ {c,d}, grows as Ω(N / (log N)³), which
tends to infinity.

**Testable prediction**: For N = 10000, a random set S with density matching
π(N) ≈ 1229 should contain at least one product collision with probability > 0.99.
In contrast, the actual primes below 10000 have zero product collisions. -/

end CounterfactualPrimes


