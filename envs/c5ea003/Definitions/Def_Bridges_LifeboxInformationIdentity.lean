-- Prove2me | Definitions.Def_Bridges_LifeboxInformationIdentity
-- name    : Bridges_LifeboxInformationIdentity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:28:47.222695+00:00
-- url     : https://prove2.me/theorems/a755fd49-06c1-4f63-87d9-0503cbd5524c
-- title:
--   Aether Catalog definitions — Bridges_LifeboxInformationIdentity
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.LifeboxInformationIdentity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/LifeboxInformationIdentity.lean by skeleton subtraction
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

* **Finite-state ⇒ decidable.** If the input space is finite (a finite-state automaton has
  finitely many observable stimuli) and outputs have decidable equality, then
  person-equivalence is *decidable* (`decidablePersonEquiv`, `finiteState_decidable`).

* **Contrarian: no finite test in general.** For an infinite input space (`ℕ`) *no* finite
  battery of tests can certify person-equivalence: for every finite set of probe inputs
  there are two distinct systems that agree on all of them (`no_finite_test`).  This is the
  precise sense in which the finiteness hypothesis above is *necessary*.

* **Quantum obstruction = no-cloning.**  A digital Lifebox works by *copying* the
  information.  Quantum information cannot be copied: there is **no** linear map
  `C : V → V ⊗ V` with `C x = x ⊗ x` for all `x`, as soon as `dim V ≥ 2`
  (`no_cloning`).  Hence a quantum brain admits no universal "read-and-duplicate" device,
  the mathematical core of the undecidability claim in the mission.

* **Kolmogorov bound is finite.**  Identities describable in `b` bits number exactly `2 ^ b`
  (`card_identities`), a finite quantity; instantiating `b = 10 ^ 15` gives the mission's
  `~10^15`-bit bound as an explicit finite cardinality (`lifebox_bound`).
-/

namespace Lifebox

/-! ## 1. Person-equivalence and the equivalence relation -/

/-- Two systems `f g : I → O` are **person-equivalent** if they produce the same output for
every input: identity is functional behaviour, not substrate. -/
def PersonEquiv {I O : Type*} (f g : I → O) : Prop := ∀ i, f i = g i




/-
Person-equivalence coincides with equality of functions (extensionality).
-/


/-! ## 2. Finite-state ⇒ person-equivalence is decidable -/

/-- If the stimulus space is finite and outputs have decidable equality, then
person-equivalence is decidable: a finite-state person can be *tested*. -/
instance decidablePersonEquiv {I O : Type*} [Fintype I] [DecidableEq O]
    (f g : I → O) : Decidable (PersonEquiv f g) :=
  Fintype.decidableForallFintype

/-
The finite-state Lifebox theorem: person-equivalence of finite-state systems is decided
by computing the finite set of *distinguishing stimuli* and checking it is empty.
-/

/-! ## 3. Contrarian: for infinite input spaces, no finite test suffices -/

/-
**No finite test.** For any finite set `S` of probe inputs there exist two *distinct*
Boolean systems `f ≠ g` that agree on every probe in `S`.  Thus over an infinite input
space person-equivalence cannot be certified by any finite battery of tests — the finiteness
hypothesis in `finiteState_decidable` is essential.
-/

/-! ## 4. Quantum obstruction: the no-cloning theorem

A Lifebox duplicates a person by copying information.  In a two-dimensional (or larger)
quantum state space there is no *linear* cloning map `x ↦ x ⊗ x`. -/

open scoped TensorProduct

/-
**No-cloning theorem.** Over any field `k`, there is no `k`-linear map
`C : k² → k² ⊗ k²` satisfying `C x = x ⊗ x` for every state `x`.  A quantum brain therefore
admits no universal duplicator: the physical basis of the mission's quantum
"undecidability" claim.
-/

/-! ## 5. Kolmogorov complexity of identity is finite and bounded -/

/-- Identities describable in `b` bits, modelled as bit-vectors `Fin b → Bool`. -/
abbrev Identity (b : ℕ) := Fin b → Bool

/-
**Finiteness / counting bound.** There are exactly `2 ^ b` identities describable in `b`
bits — a finite number.  This is the Kolmogorov counting principle for the Lifebox.
-/

/-
**Lifebox bound.** Under Rucker's `~10^15`-bit hypothesis, the number of distinct
possible identities is the finite quantity `2 ^ (10 ^ 15)`; in particular the type of such
identities is finite.
-/

end Lifebox


