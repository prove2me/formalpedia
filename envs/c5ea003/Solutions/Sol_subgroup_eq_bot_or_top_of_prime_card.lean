-- Prove2me | solution 1 for subgroup_eq_bot_or_top_of_prime_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:23:29.142671+00:00
-- url     : https://prove2.me/submissions/ad26b777-65a4-428f-a0c4-c6dfafc1a45e

-- Sol generated from Applications/Algebra/HilbertClassFieldNoIntermediates.lean
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



theorem solution    {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p)
    (S : Subgroup G) : S = ⊥ ∨ S = ⊤ := by
  -- `G` is finite since its cardinality `p` is nonzero.
  have hfin : Finite G := by
    have : Nat.card G ≠ 0 := by rw [hG]; exact hp.ne_zero
    exact Nat.finite_of_card_ne_zero this
  -- Lagrange: `|S|` divides `|G| = p`.
  have hdvd : Nat.card S ∣ Nat.card G := Subgroup.card_subgroup_dvd_card S
  rw [hG] at hdvd
  -- A divisor of a prime is `1` or `p`.
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hpc
  · exact Or.inl (Subgroup.eq_bot_of_card_le S (le_of_eq h1))
  · exact Or.inr (Subgroup.eq_top_of_card_eq S (by rw [hpc, hG]))
