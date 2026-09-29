-- Prove2me | solution 1 for hilbertClassFieldNoIntermediates
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:26:23.655441+00:00
-- url     : https://prove2.me/submissions/14aabca7-1ae6-411a-a8b2-a794ba6a8657

-- Sol generated from Applications/Algebra/HilbertClassFieldNoIntermediates.lean
import Mathlib
import Theorems.Thm_subgroup_eq_bot_or_top_of_prime_card
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



theorem solution    (K : Type*) [Field K] [NumberField K]
    (H : Type*) [Field H] [Algebra K H] [FiniteDimensional K H] [IsGalois K H]
    (e : (H ≃ₐ[K] H) ≃* ClassGroup (RingOfIntegers K))
    (p : ℕ) (hp : p.Prime) (hclass : classNumber K = p) :
    ∀ L : IntermediateField K H, L = ⊥ ∨ L = ⊤ := by
  -- Step (1): via Artin reciprocity, the Galois group has prime order `p`.
  have hcard : Nat.card (H ≃ₐ[K] H) = p := by
    have h2 : Nat.card (H ≃ₐ[K] H) = Nat.card (ClassGroup (RingOfIntegers K)) :=
      Nat.card_congr e.toEquiv
    have h3 : Nat.card (ClassGroup (RingOfIntegers K)) = classNumber K := by
      rw [Nat.card_eq_fintype_card]; rfl
    rw [h2, h3, hclass]
  intro L
  -- The Galois correspondence: an order-reversing iso `IntermediateField K H ≃o (Subgroup Gal)ᵒᵈ`.
  set φ := IsGalois.intermediateFieldEquivSubgroup (F := K) (E := H)
  -- Step (2): the subgroup `φ L` is `⊥` or `⊤` by prime-order subgroup analysis.
  have hS := subgroup_eq_bot_or_top_of_prime_card hp hcard (OrderDual.ofDual (φ L))
  rcases hS with hbot | htop
  · -- `φ L = ⊥` as a subgroup ⇒ `φ L = ⊤` in the dual `= φ ⊤` ⇒ `L = ⊤`.
    right
    apply φ.injective
    rw [φ.map_top]
    apply OrderDual.ofDual.injective
    rw [hbot]; rfl
  · -- `φ L = ⊤` as a subgroup ⇒ `φ L = ⊥` in the dual `= φ ⊥` ⇒ `L = ⊥`.
    left
    apply φ.injective
    rw [φ.map_bot]
    apply OrderDual.ofDual.injective
    rw [htop]; rfl
