-- Prove2me | Definitions.Def_Applications_LifeboxInformationIdentity
-- name    : Applications_LifeboxInformationIdentity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:51:25.109987+00:00
-- url     : https://prove2.me/theorems/390e4aac-f0f9-489e-aeb7-f5234b909a4e
-- title:
--   Aether Catalog definitions — Applications_LifeboxInformationIdentity
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.LifeboxInformationIdentity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/LifeboxInformationIdentity.lean by skeleton subtraction
import Mathlib

/-! # Rucker's Lifebox: Information-Theoretic Identity

This file formalizes several claims surrounding Rudy Rucker's *Lifebox* idea — that a
person's identity is determined by their *information content* (their input/output
behaviour) rather than by their physical substrate.

We make the following precise and prove them.

* **Person-equivalence = functional equivalence.** Two "systems" (functions from an input
  type to an output type) are *person-equivalent* when they produce the same output for
  every input.  We show this is an equivalence relation (`PersonEquiv.refl/symm/trans`,
  packaged as `personSetoid`).

* **Finite profiles ⇒ decidable.** If the complete stimulus space is finite and outputs
  have decidable equality, person-equivalence is decidable (`decidablePersonEquiv`,
  `finiteState_decidable`).  The separate `FiniteStateIdentity.lean` proves the stronger
  automata theorem for infinitely many finite input histories.

* **Contrarian: no finite test in general.** For an infinite input space (`ℕ`) *no* finite
  battery of tests can certify person-equivalence: for every finite set of probe inputs
  there are two distinct systems that agree on all of them (`no_finite_test`).  This is the
  precise sense in which the finiteness hypothesis above is *necessary*.

* **Quantum obstruction = no-cloning.** A digital Lifebox works by *copying* information.
  In the two-dimensional model there is **no** linear map `C : k² → k² ⊗ k²` with
  `C x = x ⊗ x` for every `x` (`no_cloning`). Hence a quantum state admits no universal
  linear "read-and-duplicate" device. We do **not**
  claim that this proves undecidability: no-cloning and undecidability are logically different
  notions, and no-cloning alone does not imply that an equivalence predicate is undecidable.

* **Description-space count.** Fixed-length `b`-bit descriptions number exactly `2 ^ b`
  (`card_identities`); instantiating the externally conjectured bound `b = 10 ^ 15` gives
  an explicit finite cardinality (`lifebox_bound`). This is not itself a theorem about
  machine-dependent Kolmogorov complexity.
-/

namespace Lifebox

/-! ## 1. Person-equivalence and the equivalence relation -/

/-- Two systems `f g : I → O` are **person-equivalent** if they produce the same output for
every input: identity is functional behaviour, not substrate. -/
def PersonEquiv {I O : Type*} (f g : I → O) : Prop := ∀ i, f i = g i




/-
Person-equivalence coincides with equality of functions (extensionality).
-/


/-! ## 2. Finite functional profiles have decidable person-equivalence -/

/-- If the stimulus space is finite and outputs have decidable equality, then
person-equivalence of complete functional profiles is decidable by exhaustive testing. -/
instance decidablePersonEquiv {I O : Type*} [Fintype I] [DecidableEq O]
    (f g : I → O) : Decidable (PersonEquiv f g) :=
  Fintype.decidableForallFintype

/-
For a finite complete stimulus space, person-equivalence is decided by computing the
finite set of *distinguishing stimuli* and checking that it is empty.
-/

/-! ## 3. Contrarian: for infinite input spaces, no finite test suffices -/

/-
**No finite test.** For any finite set `S` of probe inputs there exist two *distinct*
Boolean systems `f ≠ g` that agree on every probe in `S`.  Thus over an infinite input
space person-equivalence cannot be certified by any finite battery of tests — the finiteness
hypothesis in `finiteState_decidable` is essential.
-/

/-! ## 4. Further consequences of extensional identity -/




/-! ## 5. Quantum obstruction: the no-cloning theorem

A Lifebox duplicates a person by copying information. In the two-dimensional model
formalized below, there is no *linear* cloning map `x ↦ x ⊗ x`. -/

open scoped TensorProduct

/-
**No-cloning theorem.** Over any field `k`, there is no `k`-linear map
`C : k² → k² ⊗ k²` satisfying `C x = x ⊗ x` for every state `x`.  This rules out a universal linear duplicator.  It deliberately makes no
undecidability claim, because the no-cloning theorem by itself supplies none.
-/

/-! ## 6. Finite description-space counting -/

/-- Identities describable in `b` bits, modelled as bit-vectors `Fin b → Bool`. -/
abbrev Identity (b : ℕ) := Fin b → Bool

/-
**Finiteness / counting bound.** There are exactly `2 ^ b` identities describable in `b`
bits — a finite number.  This is the elementary fixed-length description counting principle.  It is not a
formalization of machine-dependent Kolmogorov complexity.
-/

/-
**Lifebox bound.** If one assumes Rucker's `~10^15`-bit hypothesis and models descriptions as
fixed-length bit-vectors, the number of possible descriptions is the finite quantity `2 ^ (10 ^ 15)`; in particular the type of such
identities is finite.
-/

end Lifebox


