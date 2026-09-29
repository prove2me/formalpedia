-- Prove2me | Definitions.Def_Geometry_HomotopyTypeTheory_Univalence
-- name    : Geometry_HomotopyTypeTheory_Univalence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:19:09.46828+00:00
-- url     : https://prove2.me/theorems/83c233eb-5286-464e-890e-4ea71a9268bf
-- title:
--   Aether Catalog definitions — Geometry_HomotopyTypeTheory_Univalence
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.HomotopyTypeTheory.Univalence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/HomotopyTypeTheory/Univalence.lean by skeleton subtraction
import Mathlib

/-!
# Univalence in Lean: functoriality, inconsistency, and the propositional fragment

The **univalence axiom** of Homotopy Type Theory asserts that the canonical map
`idToEquiv : (A = B) → (A ≃ B)` is an equivalence.  This file studies univalence *inside Lean's
own foundation* and reaches three honest conclusions.

1. **Functoriality is axiom-free.** `idToEquiv` sends `rfl` to the identity equivalence and path
   concatenation to composition of equivalences — these hold unconditionally.

2. **Full univalence is inconsistent with Lean.** Because Lean's `Eq` lives in `Prop` (so
   Axiom K / uniqueness of identity proofs holds), the existence of a univalence inverse `ua`
   leads to `False`: the two distinct self-equivalences of `Bool` (identity and negation) would
   be forced equal. This is the precise sense in which Lean is *not* a univalent foundation.

3. **The propositional fragment survives.** Restricted to mere propositions, univalence *is*
   realized in Lean — it is exactly `propext`. We exhibit the inverse `propUnivalence` and its
   round-trip law.

## Main results

* `HoTT.idToEquiv_refl`, `HoTT.idToEquiv_trans` — functoriality of `idToEquiv` (axiom-free).
* `HoTT.UnivalenceData.not_inhabited`           — full univalence is inconsistent in Lean.
* `HoTT.propUnivalence`, `HoTT.propUnivalence_idToEquiv` — the surviving propositional fragment.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer): Six conjectures were posed. (H1) `idToEquiv` is functorial without
axioms. (H2 — surprising) Full univalence is *false* in Lean, not merely unprovable. (H3) The
obstruction is exactly UIP, witnessed by the two self-equivalences of `Bool`. (H4 — surprising)
Nonetheless univalence holds for mere propositions, where it coincides with `propext`. (H5)
`idToEquiv` is injective (trivially, by UIP). (H6) Transport-of-structure would follow from
univalence but is therefore vacuous here.

EXPERIMENT (Experimenter): H1 = `Equiv.cast_refl` / `Equiv.cast_trans`. For H2/H3, assume a
univalence bundle `UnivalenceData`; since `ua e₁` and `ua e₂` are two proofs of the *same*
proposition `Bool = Bool`, proof irrelevance forces `ua (refl) = ua (neg)`, hence `refl = neg`
after applying `idToEquiv_ua`; evaluating at `true` gives `true = false`. H4 = `propext`. H6 was
abandoned: it is vacuous because `UnivalenceData` is uninhabited (H2).

ANALYSIS (Analyst): Survived: H1, H2, H3, H4. The decisive insight is that `Eq : Prop` makes the
*fibers* of `idToEquiv` subsingletons, so surjectivity onto a non-subsingleton equivalence type
is impossible. Failed/abandoned: H6 (vacuous), H5 (true but trivial, omitted as a guardrail
casualty). This pins univalence's failure on the 0-truncatedness of Lean's universe.

CRITIQUE (Critic): Is `not_inhabited` a cheap `False`-from-hypothesis trick? No — it is a
genuine derivation that *uses* the bundle's β-rule and proof irrelevance; the contradiction is
the mathematically meaningful obstruction, exactly Voevodsky's reason for needing a new
foundation. Is `propUnivalence` trivial? It crucially uses `propext`; without it the map does
not exist constructively in `Prop`.

SYNTHESIS (PI): Lean is the 0-truncated shadow of a univalent universe: univalence is functorial
but globally inconsistent, surviving precisely on propositions as `propext`.
-- !-- Lab Notes -- !--
-/

universe u

namespace HoTT

/-- The canonical map from equalities of types to equivalences. -/
def idToEquiv {A B : Type u} (h : A = B) : A ≃ B := Equiv.cast h



/-- **The univalence axiom, as a hypothesis bundle.** It provides a two-sided inverse `ua` to
`idToEquiv`. We never assert this bundle; below we *prove it is uninhabited* in Lean. -/
structure UnivalenceData where
  /-- Turn an equivalence into an equality of types. -/
  ua : ∀ {A B : Type}, (A ≃ B) → A = B
  /-- β-rule: transporting back along `ua e` recovers `e`. -/
  idToEquiv_ua : ∀ {A B : Type} (e : A ≃ B), idToEquiv (ua e) = e
  /-- η-rule: `ua` is a left inverse of `idToEquiv`. -/
  ua_idToEquiv : ∀ {A B : Type} (h : A = B), ua (idToEquiv h) = h

/-- The non-trivial self-equivalence of `Bool` given by negation; it sends `true` to `false`. -/
def negEquiv : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

namespace UnivalenceData


end UnivalenceData

/-! ### The surviving propositional fragment -/



end HoTT


