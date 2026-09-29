-- Prove2me | Definitions.Def_Logic_PosetTheory_ProofPhaseTransitions
-- name    : Logic_PosetTheory_ProofPhaseTransitions
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:00:15.207843+00:00
-- url     : https://prove2.me/theorems/5e7597f9-4f4c-4454-b4f9-860b580a3629
-- title:
--   Aether Catalog definitions — Logic_PosetTheory_ProofPhaseTransitions
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.PosetTheory.ProofPhaseTransitions`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/PosetTheory/ProofPhaseTransitions.lean by skeleton subtraction
import Mathlib
/-
# Proof Phase Transitions: Implicational Theories as Monotone Reachability

This module lays the *formal infrastructure* underpinning the program of "proof phase
transitions" for random implicational theories.  An **implicational theory** on a type
of atoms `α` is a set of single-conclusion axioms `a → b`, modelled as a binary relation
`ImplTheory α := α → α → Prop`.  **Derivability** is the reflexive–transitive closure of
the axiom relation — i.e. exactly graph reachability in the directed graph of axioms.

The headline structural facts proved here are:

* `theory_extension_monotone` / `derivable_monotone` — derivability is a **monotone**
  property of the axiom set.  This is the precise hypothesis required by Friedgut's sharp
  threshold theorem: `fun T => Derivable T a b` is a monotone Boolean function on the
  hypercube of potential edges.
* `refl_trans_gen_closed` — the **barrier method**: any set closed under the axioms and
  containing the source contains every derivable conclusion.  This is the canonical tool
  for proving *non*-derivability.
* `chain_derivable_iff` — a sharp **boundary characterization** for the linear chain
  theory: in `chainT` (the axioms `k → k+1`), `a` derives `b` iff `a ≤ b`.
* `chain_axiom_critical` — every axiom of a minimal (chain) theory is **critical**:
  deleting a single axiom destroys a derivation, while the full theory still derives it
  (`chain_axiom_restorable`).
* `chainPath_chain` / `chainPath_length` — a **constructive** witness: the explicit
  derivation `0 → 1 → ⋯ → n` of length `n`, realising the derivation as a concrete list.

-- !-- Lab Notebook -- !--
-- Hypothesis: Single-conclusion implicational derivability is *definitionally* reflexive–
--   transitive closure, hence a monotone graph-reachability property; the whole "phase
--   transition" narrative should rest on (a) monotonicity and (b) a barrier (closure)
--   lemma for non-derivability, with chains as the extremal minimal-density witnesses.
-- Result: All five pillars formalize cleanly. Monotonicity is `ReflTransGen.mono`; the
--   barrier lemma is a one-line induction on `ReflTransGen`; the chain boundary is a tight
--   iff; criticality and constructive length both follow from the barrier/chain machinery.
-- Insight: The barrier lemma `refl_trans_gen_closed` is the single reusable engine — both
--   "no backward derivation" and "deleted axiom blocks the proof" are instances of picking
--   the right closed set (`{k | a ≤ k}` resp. `{k | k ≤ m}`). Non-derivability proofs
--   reduce to exhibiting an invariant cut, exactly mirroring potential-function arguments.
-- Failure analysis: Initial `omega` calls failed because the edge relation `chainT x y`
--   was not unfolded in the closure hypothesis; `simp only [chainT]` before `omega` fixes
--   it. `List.Chain'` is deprecated in this toolchain — `List.IsChain` +
--   `List.isChain_iff_getElem` is the current API for the constructive path witness.
-- !-- end Lab Notebook -- !--
-/

open Relation

namespace ProofPhaseTransitions

/-- An **implicational theory** on atoms of type `α`: the set of single-conclusion axioms
`a → b`, encoded as a binary relation. -/
abbrev ImplTheory (α : Type*) := α → α → Prop

/-- **Derivability** in a theory `T`: the reflexive–transitive closure of the axiom
relation. Equivalently, reachability in the directed graph whose edges are the axioms. -/
def Derivable {α : Type*} (T : ImplTheory α) : α → α → Prop := ReflTransGen T




-- !-- Monotonicity: enlarging the axiom set can only enlarge the set of derivable pairs;
-- this is `ReflTransGen.mono`, the exact hypothesis Friedgut's sharp-threshold theorem
-- requires of a monotone Boolean function on the edge hypercube. -- !--


-- !-- Barrier method: a one-step induction on the reflexive-transitive closure shows any
-- set closed under the axioms and containing the source absorbs every conclusion; this is
-- the universal certificate for NON-derivability. -- !--

/-! ### The linear chain theory — the minimal-density extremal case -/

/-- The **chain theory** on `ℕ`: the axioms are exactly `k → k+1`. This is the minimal
theory making `0` derive `n`, with a derivation of length precisely `n`. -/
def chainT : ImplTheory ℕ := fun a b => b = a + 1

-- !-- Forward direction of the chain boundary: induct on the target; either the source is
-- already strictly below and we extend a shorter derivation, or source = target. -- !--


-- !-- Backward direction via the barrier lemma with the upward-closed cut `{k | a ≤ k}`:
-- the axioms only ever increase the index, so derivability cannot decrease it. -- !--



/-! ### Axiom criticality -/

/-- The chain theory with the single axiom `m → m+1` **deleted**. -/
def chainMinus (m : ℕ) : ImplTheory ℕ := fun a b => b = a + 1 ∧ a ≠ m


-- !-- Criticality via the barrier lemma with the downward-closed cut `{k | k ≤ m}`: with the
-- axiom `m → m+1` removed, no remaining axiom can escape the prefix `{0,…,m}`, so any target
-- `n > m` is unreachable. -- !--


/-! ### Constructive derivation witness -/

/-- The explicit derivation path `0 → 1 → ⋯ → n`, as a concrete list of atoms. -/
def chainPath (n : ℕ) : List ℕ := List.range (n + 1)

-- !-- The list `[0,1,…,n]` is a genuine `chainT`-chain since consecutive entries of
-- `List.range` differ by one; computed directly from `getElem_range`. -- !--


end ProofPhaseTransitions


