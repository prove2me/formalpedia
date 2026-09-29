-- Prove2me | Theorems.Thm_subgroup_eq_bot_or_top_of_prime_card
-- name    : subgroup_eq_bot_or_top_of_prime_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:10:11.554253+00:00
-- url     : https://prove2.me/theorems/288f9a59-af01-4302-9a0e-34a37759785e
-- title:
--   Subgroups of a group of prime order.
-- statement:
--   **Subgroups of a group of prime order.**  If a group `G` has prime cardinality `p`, then every
--   subgroup of `G` is either the trivial subgroup `⊥` or the whole group `⊤`.
--
--   This is pure subgroup analysis: by Lagrange's theorem the order of any subgroup divides
--   `Nat.card G = p`, and since `p` is prime this order is `1` (forcing `⊥`) or `p` (forcing `⊤`).
--
--   ```lean
--   theorem subgroup_eq_bot_or_top_of_prime_card    {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p)
--       (S : Subgroup G) : S = ⊥ ∨ S = ⊤ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/Algebra/HilbertClassFieldNoIntermediates.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/Algebra/HilbertClassFieldNoIntermediates.lean#L41

-- Thm stub generated from Applications/Algebra/HilbertClassFieldNoIntermediates.lean
import Mathlib
/-
# The Hilbert class field of prime class number has no intermediate fields

Let `K` be a number field with Hilbert class field `H`, the maximal unramified abelian extension
of `K`.  Its defining arithmetic property is the **Artin reciprocity isomorphism**

  `Gal(H/K) ≃ Cl(𝒪_K)`

between the Galois group and the ideal class group of the ring of integers (see
`Catalog.Novelty.HilbertClassFieldReciprocity`, which packages this isomorphism as the load-bearing
hypothesis `e : Gal(H/K) ≃* ClassGroup 𝒪_K` and derives the degree identity `[H:K] = h_K`).

Here we push that interface one structural step further.  Suppose the class number `h_K = p` is a
**prime**.  Then:

* via Artin reciprocity, `Gal(H/K)` is a group of prime order `p`;
* a finite group of prime order has no subgroups other than `⊥` and `⊤` — this is elementary
  subgroup analysis (Lagrange: the order of a subgroup divides `p`, hence is `1` or `p`), recorded
  as `subgroup_eq_bot_or_top_of_prime_card`;
* transporting this through the Galois correspondence
  (`IsGalois.intermediateFieldEquivSubgroup`, an order-reversing isomorphism between intermediate
  fields and subgroups of the Galois group) shows that every intermediate field of `H/K` is either
  `⊥` (i.e. `K`) or `⊤` (i.e. `H`).

The main result is `hilbertClassFieldNoIntermediates`.

## Notes on the argument

* The prime-order subgroup fact is proved from scratch by Lagrange's theorem and primality, rather
  than being imported as a black box, matching item (2) of the specification.
* No appeal is made to any generic "an intermediate field of a degree-prime extension is `⊥` or `⊤`"
  lemma (there is no `intermediate_eq_bot_or_top` in scope); the conclusion is obtained directly
  from the *subgroup* dichotomy transported across the Galois correspondence, avoiding circularity
  (item (3)).
* The Artin reciprocity datum enters only through the group isomorphism `e`, exactly the interface
  established in `Catalog.Novelty.HilbertClassFieldReciprocity` (item (1)).
-/

open NumberField

theorem subgroup_eq_bot_or_top_of_prime_card    {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p)
    (S : Subgroup G) : S = ⊥ ∨ S = ⊤ := by sorry
