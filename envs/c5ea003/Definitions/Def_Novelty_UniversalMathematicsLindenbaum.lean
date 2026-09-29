-- Prove2me | Definitions.Def_Novelty_UniversalMathematicsLindenbaum
-- name    : Novelty_UniversalMathematicsLindenbaum
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:44:35.75099+00:00
-- url     : https://prove2.me/theorems/0ba5866f-753f-43f6-86a9-7dad4539d321
-- title:
--   Aether Catalog definitions — Novelty_UniversalMathematicsLindenbaum
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.UniversalMathematicsLindenbaum`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/UniversalMathematicsLindenbaum.lean by skeleton subtraction
import Mathlib

/-!
# Maximal consistent extensions and the finite character of consistency

This file deepens the study of *universal mathematics* — the theorems shared by
every consistent theory extending a base — by adding the one structural
ingredient that makes the theory of consistent extensions genuinely rich:
**compactness**.  A consequence operator is compact when every entailment
already follows from a *finite* portion of the assumptions.  This is the abstract
shadow of the fact that proofs are finite objects.

With compactness in hand we prove two results that a syntax-free intelligence
would need in order to reason about the space of consistent extensions of its
mathematics:

* `lindenbaum` — **every consistent theory extends to a maximal consistent
  one**, which is moreover deductively closed.  The proof is an order-theoretic
  Zorn's-lemma argument: the union of a chain of consistent theories is again
  consistent precisely *because* consistency has finite character.  This is the
  bridge between the lattice theory of theories and the logic of provability.

* `consistent_iff_finite` — **consistency has finite character**: a theory is
  consistent if and only if each of its finite sub-theories is.  This is the
  exact sense in which consistency, and hence membership in the universal core,
  can be certified by finite means.

An explicit compact model (`idProofSystem`) witnesses that the axioms — including
compactness — are jointly satisfiable, so none of the results are vacuous.
-/

open Set

/-- A **compact proof system**: a Tarski consequence operator `C` together with a
distinguished absurd statement `bot`, in which every consequence follows from a
*finite* set of assumptions.  Finiteness of `compact` is the abstract trace of
the finiteness of proofs. -/
structure ProofSystem (S : Type*) where
  /-- The consequence (deductive closure) operator. -/
  C : Set S → Set S
  /-- Assumptions are among their own consequences. -/
  subset_closure : ∀ Γ, Γ ⊆ C Γ
  /-- More assumptions, more consequences. -/
  mono : ∀ ⦃Γ Δ : Set S⦄, Γ ⊆ Δ → C Γ ⊆ C Δ
  /-- Consequences of consequences are consequences (cut). -/
  idem : ∀ Γ, C (C Γ) ⊆ C Γ
  /-- A distinguished absurd statement marking inconsistency. -/
  bot : S
  /-- Compactness: every consequence follows from a finite set of assumptions. -/
  compact : ∀ {Γ : Set S} {φ : S}, φ ∈ C Γ →
    ∃ Γ₀ : Set S, Γ₀ ⊆ Γ ∧ Γ₀.Finite ∧ φ ∈ C Γ₀

namespace ProofSystem

variable {S : Type*} (P : ProofSystem S)


/-- A theory is **consistent** when it does not entail the absurd statement. -/
def Consistent (Γ : Set S) : Prop := P.bot ∉ P.C Γ





end ProofSystem

/-!
## An explicit compact model witnessing non-vacuity

The identity consequence operator on `ℕ` is compact: any consequence `φ` of `Γ`
lies in `Γ`, hence follows from the finite subset `{φ}`.  Taking `bot := 0`, a
theory is consistent exactly when it omits `0`.
-/

/-- The identity consequence system on `ℕ`, made into a compact proof system with
absurd statement `0`. -/
def idProofSystem : ProofSystem ℕ where
  C := id
  subset_closure _ := subset_rfl
  mono := fun _ _ h => h
  idem _ := subset_rfl
  bot := 0
  compact := by
    intro Γ φ hφ
    exact ⟨{φ}, by simpa using hφ, Set.finite_singleton φ, rfl⟩

namespace idProofSystem



end idProofSystem

/-!
-- !-- Lab Notes -- !--

**Hypothesis (Hypothesizer).**  If the space of consistent extensions of a base
theory is to behave well — in particular, if the "universal core" of shared
theorems is to be certifiable by finite means — then consistency must be a
*finite-character* property, and every consistent theory ought to sit inside a
maximal coherent one.  Bold claim: both facts follow from a single abstract
input, compactness, with no appeal to a specific logical syntax.

**Experiment (Experimenter).**  We axiomatised compactness directly on the
consequence operator (`ProofSystem.compact`).  The finite-character theorem
`consistent_iff_finite` then dropped out by pushing an entailment of `bot`
through `compact` and back through monotonicity.  For `lindenbaum` we ran Zorn's
lemma on the poset of consistent extensions ordered by inclusion; the only
non-formal step is that the union of a chain of consistent theories is
consistent, isolated as `sUnion_chain_consistent`.

**Analysis (Analyst).**  The chain lemma is exactly where compactness pays off:
a hypothetical derivation of `bot` from the union uses only finitely many
assumptions, which — the chain being directed — all live in a single member,
contradicting that member's consistency.  A pleasant surprise was that the
maximal element produced by Zorn is automatically deductively *closed*: its
closure is a consistent superset, so maximality forces closure to add nothing.
Thus "maximal consistent" and "maximal consistent *and closed*" coincide for
free.

**Critique (Critic).**  Is compactness doing real work, or is it decorative?
Real work: without it the chain lemma fails and Zorn cannot start.  Is the whole
development vacuous?  No: `idProofSystem` is an explicit compact model with a
consistent theory `{1}` (`singleton_consistent`) that provably extends to a
maximal consistent theory (`exists_maximal`).  Does `lindenbaum` secretly assume
`Nonempty S`?  No — the base `base` is a witness-carrying set and Zorn is applied
to a family that already contains it, so the argument runs even for exotic
carriers, needing no separate nonemptiness hypothesis.

**Synthesis (Principal Investigator).**  Compactness is the hinge on which the
theory of consistent extensions turns.  It makes consistency finitely
certifiable and guarantees maximal coherent completions.  Combined with the
extension-invariance results, the picture is: the universal core is the base
theory, consistent extensions can enrich it in many maximal ways, and every one
of those ways is reachable and finitely policed.  A non-human mathematics built
on compact reasoning would face exactly the same landscape.
-/


