-- Prove2me | Definitions.Def_Speculative_NumberTheory_IsomorphismsOfMeaning
-- name    : Speculative_NumberTheory_IsomorphismsOfMeaning
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:33:53.452386+00:00
-- url     : https://prove2.me/theorems/10d75d64-5308-48a4-a25f-890a5240bc5f
-- title:
--   Aether Catalog definitions — Speculative_NumberTheory_IsomorphismsOfMeaning
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.NumberTheory.IsomorphismsOfMeaning`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/NumberTheory/IsomorphismsOfMeaning.lean by skeleton subtraction
import Mathlib

/-!
# Isomorphisms of Meaning: When Structures Collide

This file formalizes, in the concrete setting of additive groups (and the cyclic
groups `ZMod n` in particular), the philosophical thesis that *isomorphic
structures preserve all structural truth yet fail to pin down the individual
"meaning" of their elements*.

The mathematical backbone is the observation that the collection of isomorphisms
between two isomorphic objects is a **torsor** over the automorphism group of
either endpoint.  Concretely:

* `autEquivIsoDom`, `isoEquivAutCod` — the "isomorphism of isomorphisms": the set
  of all identifications `G ≃+ H` is in canonical bijection with the automorphism
  group of the domain (and of the codomain), once *any one* identification is
  fixed.  There is no canonical basepoint, exactly as in a torsor.
* `iso_diff_by_aut`, `aut_unique_of_trans_eq` — any two identifications differ by
  a unique automorphism.

**Truth is preserved.**  Every structural predicate is transported across an
isomorphism:

* `transport_addOrderOf` — element orders are preserved;
* `transport_isAddCyclic` — cyclicity is preserved;
* `transport_card` — cardinality is preserved;
* `structural_invariance` — *any* isomorphism-invariant predicate `P` satisfies
  `P G ↔ P H`.  No formal system whose predicates respect isomorphism can tell
  `G` and `H` apart.

**Meaning is not preserved.**  The identification is genuinely ambiguous whenever
the automorphism group is nontrivial:

* `negAut_ne_refl` — negation is a nontrivial automorphism of `ZMod n` (`n ≥ 3`),
  so `+1` and `-1` play interchangeable structural roles: no formal predicate can
  distinguish them;
* `nonunique_identification` — a nontrivial automorphism yields a genuinely
  different identification;
* `card_aut_zmod`, `card_iso_to_zmod` — the number of distinct identifications of
  a cyclic group with `ZMod n` is exactly Euler's totient `φ(n)`.  "Meaning" is
  `φ(n)`-fold ambiguous.

**Structures that should not collide, do not.**  The order-spectrum invariant is
strong enough to *separate* non-isomorphic groups of equal size:

* `crtCollision` — the Chinese Remainder Theorem exhibits `ZMod 6` and
  `ZMod 2 × ZMod 3` as the *same* structure wearing two different faces;
* `no_iso_klein` — yet `ZMod 4` and the Klein four-group `ZMod 2 × ZMod 2` are
  *not* isomorphic, distinguished by whether an element of order `4` exists.

This is the number-theoretic shadow of Hofstadter's Copycat architecture: an
analogy ("do to `H` what the isomorphism does to `G`") is fixed only up to the
symmetry group of the target; the "slippage" between equally valid analogies is
measured precisely by the automorphism group.
-/

namespace IsoMeaning

variable {G H K : Type*} [AddGroup G] [AddGroup H] [AddGroup K]

/-! ## The isomorphism of isomorphisms (torsor structure) -/


/-- **Isomorphism of isomorphisms (codomain version).**  The identifications
`G ≃+ H` are in canonical bijection with the automorphisms of the codomain `H`,
via `f ↦ e.symm.trans f`. -/
def isoEquivAutCod (e : G ≃+ H) : (G ≃+ H) ≃ (H ≃+ H) where
  toFun f := e.symm.trans f
  invFun u := e.trans u
  left_inv f := by ext x; simp
  right_inv u := by ext x; simp



/-! ## Truth is preserved: structural invariants transport -/





/-! ## Meaning is not preserved: ambiguity of the identification -/


/-! ## Number-theoretic incarnations -/



/-- **Structures collide (CRT).**  The Chinese Remainder Theorem exhibits
`ZMod 6` and `ZMod 2 × ZMod 3` as one and the same additive structure wearing
two semantically different faces (a single residue vs. a pair of residues). -/
noncomputable def crtCollision : ZMod 6 ≃+ ZMod 2 × ZMod 3 :=
  (ZMod.chineseRemainder (show Nat.Coprime 2 3 by decide)).toAddEquiv




/-! ## Non-collision: structural invariants separate distinct structures -/



end IsoMeaning


