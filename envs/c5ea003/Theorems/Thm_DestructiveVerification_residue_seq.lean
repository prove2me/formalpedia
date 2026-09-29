-- Prove2me | Theorems.Thm_DestructiveVerification_residue_seq
-- name    : DestructiveVerification.residue_seq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:10:29.571689+00:00
-- url     : https://prove2.me/theorems/6b1f708b-e90e-47cc-be9a-1136d32efb37
-- title:
--   Residue seq
-- statement:
--   Formal statement of `DestructiveVerification.residue_seq` from the Aether Catalog (Combinatorics). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem DestructiveVerification.residue_seq(t₁ t₂ : Test D) (d : D) :
--       residue (seq t₁ t₂) d = residue t₂ (residue t₁ d) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/DestructiveVerification.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/DestructiveVerification.lean#L228

-- Thm stub generated from Combinatorics/DestructiveVerification.lean
import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
/-
# Destructive verification: verdicts with a residual dish

A *verification* is usually modelled as a predicate: you hand a checker an object
and it says `true` or `false`.  That model silently assumes the object survives
the check.  Many real verification procedures do not have this property — a
destructive material test, a measurement that collapses the state, a one-shot
consumable certificate.

This file formalises verification as a **state transition**

  `t : D → Bool × D`,

a *test* on a type `D` of **dishes**, returning both a **verdict** `verdict t d`
and a **residual dish** `residue t d`.  The point of the model is that it lets
one *separate*, by theorems rather than by decree, three notions that the
predicate model conflates:

* `Nondestructive t` — the dish comes back untouched (`residue t d = d`);
* `Reversible t`     — the dish is transformed but nothing is lost
                       (`residue t` is a bijection);
* `Repeatable t`     — re-running the test on the residue gives the same verdict.

The main results are:

* `DestructiveVerification.Nondestructive.reversible`,
  `DestructiveVerification.Nondestructive.repeatable_iterate` — nondestructive
  tests sit at the bottom of the hierarchy: they are reversible and their
  verdict is invariant under arbitrarily many re-runs.
* `DestructiveVerification.reversible_not_nondestructive`,
  `DestructiveVerification.repeatable_not_reversible`,
  `DestructiveVerification.reversible_not_repeatable` — all three inclusions
  are **strict**, witnessed by explicit two-dish counterexamples.  So no
  implication beyond the proved ones holds.
* `DestructiveVerification.seq_assoc`, `seq_one`, `one_seq` — sequential
  composition (run one test, then the other on the residue, and conjoin the
  verdicts) is a monoid, and `nondestructive_seq` shows the nondestructive
  tests form a submonoid.
* `DestructiveVerification.seq_comm_of_nondestructive` versus
  `DestructiveVerification.seq_not_comm` — **certificates commute, destructive
  tests do not**.  This is the sharpest form of the separation: with
  nondestructive tests the order of a verification battery is irrelevant, and
  that fails as soon as one test is destructive.
* `DestructiveVerification.Repeatable.detects_invariant` — a repeatable test
  that decides a property `P` necessarily *preserves* `P`; destruction is
  constrained by repeatability even though it is not forbidden by it.
* `DestructiveVerification.card_tests`, `card_nondestructive`,
  `card_nondestructive_lt_card_tests` — a counting separation:
  there are `(2n)^n` tests on an `n`-dish type but only `2^n` certificates, so
  for `n ≥ 2` certificates are a strictly (indeed exponentially) small minority.

Nothing here assigns a hardness label to any of the three classes; the content
is purely the structural taxonomy and its strictness.
-/

open DestructiveVerification

open Finset

variable {D : Type*}

/-! ## 1. Tests, verdicts, residues -/







/-! ## 2. The three classes -/






/-! ## 3. The proved implications -/







/-! ## 4. Strictness of the hierarchy: two-dish counterexamples -/













/-! ## 5. Sequential composition: the verification monoid -/




@[simp]

theorem DestructiveVerification.residue_seq(t₁ t₂ : Test D) (d : D) :
    residue (seq t₁ t₂) d = residue t₂ (residue t₁ d) := by sorry
