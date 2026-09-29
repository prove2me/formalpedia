-- Prove2me | Definitions.Def_Bridges_EntropyClosureSeparation
-- name    : Bridges_EntropyClosureSeparation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:20:11.870467+00:00
-- url     : https://prove2.me/theorems/52806415-3e60-49cd-b6bc-55f7798c546b
-- title:
--   Aether Catalog definitions — Bridges_EntropyClosureSeparation
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.EntropyClosureSeparation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/EntropyClosureSeparation.lean by skeleton subtraction
import Mathlib

/-!
# Entropy-Rate Separation via Closure Growth Dynamics

This file formalizes the mathematical core of **closure-growth separation**: the principle
that two monotone set transformers (modeling proof-search policies) can be distinguished
by a finite witness whenever their iterated closures diverge at any stage.

## Main results

### Abstract closure iteration theory
- `closureIter`: iteration of a set transformer via `Nat.iterate`
- `closureIter_zero`, `closureIter_succ_apply`: standard recursion lemmas
- `closureIter_mono`: monotonicity propagates through iteration
- `closureIter_stabilizes`: idempotent closure operators stabilize in one step

### Witness extraction
- `finite_witness_of_stage_separation`: any stage where `F^[n] S ⊈ G^[n] S` yields
  a concrete element witnessing the separation
- `finite_witness_of_eventual_growth_gap`: eventual strict inclusion implies a
  finite separating witness

### Fixed-point invariance
- `closure_fixed_points_are_iterative_invariants`: fixed points of a closure operator
  are invariant under all iterates

### EML instantiation
- `fullEMLClosure'_extensive`: seed sets embed into their full EML closure
- `fullEMLClosure'_setMono`: full EML closure is monotone in the seed set
- `fullEMLClosure'_isClosureOp`: full EML closure is a closure operator
- `fullEMLClosure'_iter_stabilizes`: iterates of full EML closure stabilize

## Motivation

In neural proof mining, a **proof policy** induces a set transformer on the space of
proof states: given a set of reachable states, the policy expands it by one step of
search. The **closure filtration** `F^[0] S ⊆ F^[1] S ⊆ ⋯` captures the cumulative
reach of the policy from seed set `S`.

Two policies `F` and `G` are **separable** if their filtrations diverge: some state is
reachable by `F` but not by `G` (or vice versa) within finitely many steps. The
**finite witness theorem** (`finite_witness_of_stage_separation`) extracts a concrete
certificate of this divergence — the exact mathematical object needed for
counterexample-guided training and benchmark generation.

The split between **preclosure** dynamics (monotone + extensive, where growth happens)
and **closure** saturation (idempotent, where growth halts) is the formal kernel of
"thermodynamic proof complexity": entropy lives in the transient filtration, while
semantic invariants live in the idempotent hull.
-/

open Set Function

noncomputable section

namespace ClosureGrowth

/-! ## Definitions: Set Monotonicity, Closure, and Preclosure -/

/-- A set transformer is **monotone** if it preserves subset inclusion. -/
def SetMono {α : Type*} (C : Set α → Set α) : Prop :=
  ∀ ⦃S T : Set α⦄, S ⊆ T → C S ⊆ C T

/-- A **preclosure operator** is monotone and extensive (inflationary).
    This models a single-step expansion of a proof-search policy. -/
structure IsPreclosureOp {α : Type*} (F : Set α → Set α) : Prop where
  extensive : ∀ S, S ⊆ F S
  monotone : SetMono F

/-- A **closure operator** is a preclosure operator that is additionally idempotent.
    Fixed points of a closure operator are the "learnable invariant strategies." -/
structure IsClosureOp {α : Type*} (C : Set α → Set α) : Prop where
  extensive : ∀ S, S ⊆ C S
  monotone : SetMono C
  idempotent : ∀ S, C (C S) = C S


/-! ## Iterated Closure -/

/-- Iterate a set transformer `C` by `n`-fold self-composition. -/
def closureIter {α : Type*} (C : Set α → Set α) (n : ℕ) : Set α → Set α :=
  C^[n]



/-! ## Monotonicity of Iterates -/


/-! ## Extensivity of Iterates -/




/-! ## Stabilization for Closure Operators -/


/-! ## Stagewise Reachability and Witness Extraction -/



/-! ## Eventual Growth Gap and Separation -/

/-- Two transformers exhibit an **eventual growth gap** from seed `S` if,
    past some threshold, `G` is strictly contained in `F` at every stage. -/
def EventuallyStrictlyLarger {α : Type*}
    (F G : Set α → Set α) (S : Set α) : Prop :=
  ∃ N, ∀ n ≥ N, closureIter G n S ⊂ closureIter F n S


/-! ## Fixed-Point Invariance -/

/-- A set `S` is **invariant** under `C` if `C S = S`. -/
def IsInvariant {α : Type*} (C : Set α → Set α) (S : Set α) : Prop :=
  C S = S



/-! ## EML Closure Infrastructure

We reproduce the core EML definitions here for self-containedness, then
connect them to the abstract closure theory. The EML (Exponential-Minus-Log)
operation generates a closure on `Set ℝ` modeling compositional proof-state
transformations.
-/

/-- The EML operation: `EMLd'(a, b) = exp(a) - log(b)`. -/
def EMLd' (a b : ℝ) : ℝ := Real.exp a - Real.log b

/-- EML closure at depth `n`: start from seed set `S` and iteratively adjoin
    all values obtainable by applying `EMLd'` to pairs of existing elements. -/
def EMLClosure' : ℕ → Set ℝ → Set ℝ
  | 0, S => S
  | n + 1, S => EMLClosure' n S ∪
      {z | ∃ a ∈ EMLClosure' n S, ∃ b ∈ EMLClosure' n S, z = EMLd' a b}

/-- The full EML closure: union over all depths. -/
def fullEMLClosure' (S : Set ℝ) : Set ℝ := ⋃ n, EMLClosure' n S








/-
Key lemma: elements of `EMLClosure' n (fullEMLClosure' S)` are in `fullEMLClosure' S`.
    This is the core of the idempotence proof.
-/





end ClosureGrowth

end


