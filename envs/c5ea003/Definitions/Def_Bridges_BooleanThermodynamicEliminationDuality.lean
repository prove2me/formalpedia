-- Prove2me | Definitions.Def_Bridges_BooleanThermodynamicEliminationDuality
-- name    : Bridges_BooleanThermodynamicEliminationDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:15:21.871329+00:00
-- url     : https://prove2.me/theorems/1e2617bb-c408-41c1-b795-82a9951dff1b
-- title:
--   Aether Catalog definitions — Bridges_BooleanThermodynamicEliminationDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.BooleanThermodynamicEliminationDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/BooleanThermodynamicEliminationDuality.lean by skeleton subtraction
import Mathlib

/-!
# Boolean Thermodynamic–Elimination Duality for Closure-Generated Proof Semirings
  via Join-Irreducible Prime Coding

## Overview

In a finite distributive lattice, the order relation is completely determined by
sup-irreducible (join-irreducible) elements. This file leverages this fundamental
fact of Birkhoff's representation theory to establish a duality between:

1. **Elimination soundness/completeness**: Derivability after variable elimination
   is equivalent to passing all sup-irreducible prime tests.
2. **Thermodynamic separation**: Non-derivability admits a maximal-energy
   sup-irreducible countermodel.

### Core Mathematical Content

The breakthrough statement is:

> In the finite distributive regime, elimination and non-derivability are governed by
> the same finite set of join-irreducible prime witnesses. Derivability after eliminating
> an auxiliary variable is equivalent to passing all join-irreducible prime tests, while
> failure of elimination derivability admits a join-irreducible prime witness that is
> simultaneously thermodynamically extremal.

This fuses:
1. Prime-spectrum semantics (sup-prime = sup-irreducible in distributive lattices)
2. Finite distributive lattice coding via Birkhoff duality
3. Elimination as projection onto a variable-free fragment
4. Free-energy separation as an optimization principle

### Main Results

* `le_iff_forall_supIrred_le` — In a finite lattice with ⊥, the order is completely
  determined by sup-irreducible elements.
* `exists_supIrred_separation` — Separation witness for non-derivability.
* `elimination_prime_code_iff` — Elimination derivability ↔ all prime codes accept.
* `exists_maximal_energy_separator` — Non-derivability yields a maximal-energy witness.
* `boolean_thermodynamic_elimination_duality` — The combined main theorem.
* `eliminationDecider_spec` — Correctness of the computable elimination decider.
* `maximalEnergyWitness_spec` — Correctness of the witness extraction procedure.
-/

open Finset Classical

noncomputable section

namespace BooleanThermodynamicElimination

/-! ## Section 1: Core Lattice Theory

The fundamental fact: in a finite sup-semilattice with ⊥, every element decomposes
into sup-irreducible elements (by `exists_supIrred_decomposition`). This means the
order is completely detected by sup-irreducible elements.

In a finite *distributive* lattice, sup-irreducible = sup-prime
(`supPrime_iff_supIrred`), giving the "prime" interpretation.
-/

/-
**Birkhoff Separation Lemma**: In a finite sup-semilattice with ⊥,
`a ≤ b` if and only if every sup-irreducible element below `a` is also below `b`.

This is the order-theoretic backbone of the elimination duality. The forward direction
is immediate by transitivity. The backward direction uses `exists_supIrred_decomposition`
to write `a` as a finite join of sup-irreducibles, each of which must be below `b`.
-/


/-! ## Section 2: Closure-Generated Proof Semiring

We model a proof system as a finite distributive lattice `L` with an embedding of
formulas. The "theory" of a context is the join of its embedded formulas. Derivability
is the lattice order.

This captures the essential structure of closure-generated proof semirings: the lattice
operations encode logical closure, and the sup-irreducible elements serve as prime
witnesses/filters.
-/

/-- A closure-generated proof semiring: a finite distributive lattice `L` equipped with
an embedding of formulas from type `α`.

The lattice `L` represents the space of theories/proof states. Each formula `φ : α`
is embedded as a lattice element `embed φ : L`, and the theory of a context `Γ` is
the join `⨆ γ ∈ Γ, embed γ`. Derivability is the lattice order.

In a distributive lattice, sup-irreducible = sup-prime, giving each sup-irreducible
element the dual role of a prime filter and a join-irreducible proof state. -/
structure ClosureProofSemiring (α : Type*) where
  /-- The lattice of theories / proof states -/
  L : Type*
  /-- The theory lattice is a distributive lattice -/
  [instDistribLattice : DistribLattice L]
  /-- The theory lattice has a bottom element (empty theory) -/
  [instOrderBot : OrderBot L]
  /-- The theory lattice is finite -/
  [instFintype : Fintype L]
  /-- The theory lattice has decidable equality -/
  [instDecEq : DecidableEq L]
  /-- Embedding of formulas into the theory lattice -/
  embed : α → L

attribute [instance] ClosureProofSemiring.instDistribLattice
  ClosureProofSemiring.instOrderBot ClosureProofSemiring.instFintype
  ClosureProofSemiring.instDecEq

variable {α : Type*} [DecidableEq α] (S : ClosureProofSemiring α)

/-- The theory generated by a finite context `Γ`: the join (sup) of all embedded formulas.
For `Γ = {γ₁, ..., γₙ}`, this is `embed γ₁ ⊔ ... ⊔ embed γₙ ⊔ ⊥`. -/
def ClosureProofSemiring.theory (Γ : Finset α) : S.L :=
  Γ.sup S.embed

/-- Derivability: `φ` is derivable from `Γ` if `embed(φ) ≤ theory(Γ)`, i.e.,
the content of `φ` is contained in the theory generated by `Γ`. -/
def Derivable (Γ : Finset α) (φ : α) : Prop :=
  S.embed φ ≤ S.theory Γ

/-- Variable elimination by erasure from the context. -/
def eliminateVar (Γ : Finset α) (y : α) : Finset α := Γ.erase y

/-! ## Section 3: Join-Irreducible Prime Witnesses

The sup-irreducible elements of the theory lattice serve as prime witnesses. In a
distributive lattice, these are exactly the sup-prime elements
(`supPrime_iff_supIrred`), justifying the "prime code" terminology.

Each prime witness `j` encodes a minimal "test" that a derivation must pass:
- `j` **accepts** if whenever `j` is a sub-aspect of `φ`'s content, `j` is already
  captured by the context's theory.
- `j` **rejects** if `j` witnesses an aspect of `φ` not captured by the context.
-/

/-- The finite set of sup-irreducible (join-irreducible) prime witnesses in the
theory lattice. These are the elements `j` satisfying `SupIrred j`: `j` is not
minimal and cannot be written as a non-trivial join. -/
def joinIrreduciblePrimeWitnesses : Finset S.L :=
  Finset.univ.filter (fun j => SupIrred j)

/-- A prime code `j` **accepts** the derivation of `φ` from context `Γₑ`:
if `j` is below `φ`'s embedding, then `j` is already below `Γₑ`'s theory.

Semantically: the aspect of proof content represented by `j` is compatible with
deriving `φ` from `Γₑ`. -/
def primeCodeAccepts (j : S.L) (Γₑ : Finset α) (φ : α) : Prop :=
  j ≤ S.embed φ → j ≤ S.theory Γₑ

/-- A prime code `j` **rejects** the derivation: `j` witnesses an aspect of `φ`
not captured by `Γₑ`'s theory. This is the negation of acceptance together with
the witness condition `j ≤ embed φ`. -/
def primeCodeRejects (j : S.L) (Γₑ : Finset α) (φ : α) : Prop :=
  j ≤ S.embed φ ∧ ¬ (j ≤ S.theory Γₑ)

/-! ## Section 4: Elimination Soundness and Completeness -/


/-
**Elimination Completeness**: If every join-irreducible prime witness accepts,
then `φ` is derivable from the eliminated context. This is the deep direction,
using the sup-irreducible decomposition of lattice elements.
-/


/-! ## Section 5: Thermodynamic Separation

When derivability fails, not only does a separating sup-irreducible witness exist,
but one can choose a *maximal-energy* witness among all separating witnesses.

The "free energy" is an abstract scoring function on lattice elements. The
thermodynamic interpretation: among all prime-code countermodels, the one with
maximal free energy is the most informative separator.
-/

/-- A free energy assignment to theory lattice elements. This abstracts the
thermodynamic scoring of countermodels. -/
structure FreeEnergyData (S : ClosureProofSemiring α) where
  /-- Energy function on lattice elements -/
  energy : S.L → ℕ

variable (E : FreeEnergyData S)

/-- A sup-irreducible `j` is a **maximal free-energy countermodel** if it rejects
the derivation and no other rejecting sup-irreducible has strictly higher energy. -/
def IsMaxFreeEnergyCountermodel (j : S.L) (Γₑ : Finset α) (φ : α) : Prop :=
  primeCodeRejects S j Γₑ φ ∧
  ∀ j' ∈ joinIrreduciblePrimeWitnesses S,
    primeCodeRejects S j' Γₑ φ → E.energy j' ≤ E.energy j

/-
**Non-derivability witness with separation**: When derivability fails, a
sup-irreducible witness exists that separates. This follows from the
`exists_supIrred_separation` lemma applied to `embed φ` and `theory Γₑ`.
-/

/-
**Maximal Energy Separator Theorem**: When derivability fails, there exists a
maximal-energy sup-irreducible countermodel. This combines the existence of a
rejecting witness with finite maximization over the energy function.
-/

/-! ## Section 6: Main Duality Theorem -/


/-! ## Section 7: Computable Decider

The prime-code characterization yields a decision procedure: check all join-irreducible
prime witnesses. Since the lattice is finite, this is a finite enumeration.
-/

/-- Computable decision procedure for elimination derivability via prime code testing.
Returns `true` iff `φ` is derivable from `eliminateVar Γ y`.

The procedure enumerates all sup-irreducible elements and checks whether each one
accepts the derivation. -/
def eliminationDecider (Γ : Finset α) (y : α) (φ : α) : Bool :=
  decide (∀ j ∈ joinIrreduciblePrimeWitnesses S, primeCodeAccepts S j (eliminateVar Γ y) φ)


/-! ## Section 8: Maximal Energy Witness Extraction

We extract a concrete maximal-energy separating witness using finite maximization
over the set of rejecting sup-irreducible elements.
-/

/-- Extract a maximal-energy separating witness, if one exists.
Returns `some j` where `j` is a sup-irreducible element that rejects the derivation
and has maximal energy among all rejecting witnesses, or `none` if there are no
rejecting witnesses (i.e., the derivation succeeds). -/
def maximalEnergyWitness (Γ : Finset α) (y : α) (φ : α) : Option S.L :=
  let Γₑ := eliminateVar Γ y
  let rejecters := (joinIrreduciblePrimeWitnesses S).filter
    (fun j => primeCodeRejects S j Γₑ φ)
  if h : rejecters.Nonempty then
    some (Finset.exists_max_image rejecters E.energy h).choose
  else none

/-
**Witness Extraction Correctness**: When derivability fails, the witness extractor
returns a concrete sup-irreducible element that rejects the derivation and has
maximal energy among all rejecting witnesses.
-/

/-! ## Section 9: Sup-Prime Interpretation

In a distributive lattice, sup-irreducible elements are exactly the sup-prime elements.
This bridges the lattice-theoretic and logical interpretations: each join-irreducible
element is also a "prime" in the logical sense.
-/


end BooleanThermodynamicElimination


