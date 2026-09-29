-- Prove2me | solution 1 for HoTT.UnivalenceData.not_inhabited
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:20:14.745989+00:00
-- url     : https://prove2.me/submissions/17b0fc64-d95b-4218-92ef-9a720173bed4

-- Sol generated from Geometry/HomotopyTypeTheory/Univalence.lean
import Mathlib
import Definitions.Def_Geometry_HomotopyTypeTheory_Univalence

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

open HoTT






open UnivalenceData



/-! ### The surviving propositional fragment -/




open HoTT.UnivalenceData in
theorem solution: UnivalenceData → False := by
  intro U
  -- `ua (refl Bool)` and `ua negEquiv` are two proofs of the same proposition `Bool = Bool`.
  have hpi : U.ua (Equiv.refl Bool) = U.ua negEquiv := Subsingleton.elim _ _
  -- Hence the equivalences they come from are equal.
  have heq : (Equiv.refl Bool) = negEquiv := by
    calc Equiv.refl Bool = idToEquiv (U.ua (Equiv.refl Bool)) := (U.idToEquiv_ua _).symm
      _ = idToEquiv (U.ua negEquiv) := by rw [hpi]
      _ = negEquiv := U.idToEquiv_ua _
  -- But they disagree at `true`.
  have : (true : Bool) = false := congrArg (fun e : Bool ≃ Bool => e true) heq
  exact Bool.noConfusion this
