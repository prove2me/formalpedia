-- Prove2me | Definitions.Def_Logic_PosetTheory_ProofRefinementFramework
-- name    : Logic_PosetTheory_ProofRefinementFramework
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:00:24.284907+00:00
-- url     : https://prove2.me/theorems/09817c68-74e7-406b-bdb0-5de144e3287d
-- title:
--   Aether Catalog definitions — Logic_PosetTheory_ProofRefinementFramework
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.PosetTheory.ProofRefinementFramework`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/PosetTheory/ProofRefinementFramework.lean by skeleton subtraction
import Mathlib

/-!
# A Proof-Refinement Framework

This file formalizes the proof-refinement framework described in the research
brief: proofs can be *simplified* over time, and we study when such a
simplification process is well behaved.

## The model

A `RefinementSystem` bundles together:

* a type `Candidate` of concrete proof candidates for a fixed target,
* a soundness predicate `valid : Candidate → Prop` (`valid c` records that `c`
  really certifies the target proposition), and
* a decidable complexity measure `complexity : Candidate → ℕ` (e.g. the size of
  the underlying Lean term, or a custom weight).

A candidate `p'` **refines** `p` when both are valid and `p'` is strictly
simpler:

```
refines p' p  :=  valid p' ∧ valid p ∧ complexity p' < complexity p
```

## Main results

* `RefinementSystem.refines_wellFounded` — refinement is well founded (it is a
  subrelation of the pullback of `<` on `ℕ` along `complexity`), so no infinite
  simplification is possible.
* `RefinementSystem.process_halts` — any deterministic, complexity-non-increasing
  refinement process eventually stabilizes in complexity.
* `RefinementSystem.exists_minimal` — as soon as a valid candidate exists, there
  is a globally complexity-minimal valid candidate.

## Counterexamples

The final two sections show that these good properties do *not* guarantee a
unique simplest proof, nor that a local process reaches the global optimum:

* `two_distinct_global_minima` — two distinct candidates that are both valid and
  both globally complexity-minimal.
* `clocal_is_local_min` together with `clocal_not_global_min` — a deterministic
  process that gets stuck at a *local* minimum even though a strictly simpler
  valid candidate exists (unreachable by the process's allowed steps).
-/

namespace ProofRefinement

/-- A *proof-refinement system* for a fixed target proposition: a type of proof
candidates, a validity (soundness) predicate, and a natural-number complexity
measure. -/
structure RefinementSystem where
  /-- The type of concrete proof candidates for the target. -/
  Candidate : Type
  /-- Soundness predicate: `valid c` means `c` genuinely certifies the target. -/
  valid : Candidate → Prop
  /-- The complexity measure (e.g. term size or a custom weight). -/
  complexity : Candidate → ℕ

namespace RefinementSystem

variable (S : RefinementSystem)

/-- `refines p' p`: the candidate `p'` is a refinement of `p`, i.e. both are
valid and `p'` is strictly simpler. -/
def refines (p' p : S.Candidate) : Prop :=
  S.valid p' ∧ S.valid p ∧ S.complexity p' < S.complexity p




end RefinementSystem

/-! ## Counterexample 1: two distinct global minima

For the (true) target `2 + 2 = 4` we build a system with two distinct valid
candidates of equal, globally minimal complexity. -/

/-- Candidates for `2 + 2 = 4`: two distinct "single-step" proofs of complexity
`1` and a verbose proof of complexity `3`. -/
inductive GMCand where
  | rflProof
  | normNumProof
  | verboseProof
  deriving DecidableEq

/-- Complexity assignment: the two single-step proofs both weigh `1`. -/
def gmComplexity : GMCand → ℕ
  | .rflProof => 1
  | .normNumProof => 1
  | .verboseProof => 3

/-- The refinement system whose target is `2 + 2 = 4`.  Since the target holds,
every candidate is valid. -/
def globalMinimaSystem : RefinementSystem where
  Candidate := GMCand
  valid := fun _ => (2 + 2 = 4)
  complexity := gmComplexity


/-! ## Counterexample 2: a local minimum that is not global

We model a deterministic process on four candidates.  The process descends
`start (5) ⇝ mid (4) ⇝ local (3)` and then gets stuck, even though a strictly
simpler valid candidate `global (2)` exists — it is simply unreachable by the
process's allowed steps.  Thus well-foundedness, halting and existence of a
global minimum do *not* imply the process reaches the global optimum. -/

/-- Candidates for the local-minimum example, with complexities `5, 4, 3, 2`. -/
inductive LMCand where
  | cstart
  | cmid
  | clocal
  | cglobal
  deriving DecidableEq

/-- Complexity weights: `start = 5`, `mid = 4`, `local = 3`, `global = 2`. -/
def lmComplexity : LMCand → ℕ
  | .cstart => 5
  | .cmid => 4
  | .clocal => 3
  | .cglobal => 2

/-- The refinement system for the local-minimum example; every candidate is
valid. -/
def localMinSystem : RefinementSystem where
  Candidate := LMCand
  valid := fun _ => True
  complexity := lmComplexity

/-- The deterministic process step.  It descends `start ⇝ mid ⇝ local` and then
loops at `local`; `global` is a separate fixed point never produced by the
process. -/
def lmNext : LMCand → LMCand
  | .cstart => .cmid
  | .cmid => .clocal
  | .clocal => .clocal
  | .cglobal => .cglobal

/-- An *allowed process step*: the deterministic successor `lmNext`, provided it
strictly decreases complexity. -/
def lmStep (p' p : LMCand) : Prop :=
  lmNext p = p' ∧ lmComplexity p' < lmComplexity p





end ProofRefinement


