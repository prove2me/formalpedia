-- Prove2me | Definitions.Def_Combinatorics_DestructiveVerification
-- name    : Combinatorics_DestructiveVerification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:32:04.813247+00:00
-- url     : https://prove2.me/theorems/b0162e7a-a1a5-414b-a41a-53b586508c73
-- title:
--   Aether Catalog definitions — Combinatorics_DestructiveVerification
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.DestructiveVerification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/DestructiveVerification.lean by skeleton subtraction
import Mathlib
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

namespace DestructiveVerification

open Finset

variable {D : Type*}

/-! ## 1. Tests, verdicts, residues -/

/-- A **test** on a type of dishes `D`: it consumes a dish and returns a verdict
together with the residual dish. -/
abbrev Test (D : Type*) := D → Bool × D

/-- The verdict returned by a test. -/
def verdict (t : Test D) (d : D) : Bool := (t d).1

/-- The residual dish left over by a test. -/
def residue (t : Test D) (d : D) : D := (t d).2


lemma test_eq (t : Test D) (d : D) : t d = (verdict t d, residue t d) := rfl

/-- Two tests are equal exactly when they agree on verdicts and on residues. -/
lemma ext_test {t₁ t₂ : Test D} (hv : ∀ d, verdict t₁ d = verdict t₂ d)
    (hr : ∀ d, residue t₁ d = residue t₂ d) : t₁ = t₂ := by
  funext d
  rw [test_eq t₁ d, test_eq t₂ d, hv d, hr d]

/-! ## 2. The three classes -/

/-- A **nondestructive** test (a *certificate check*): the dish is returned
unchanged. -/
def Nondestructive (t : Test D) : Prop := ∀ d, residue t d = d

/-- A **reversible** test: the dish is transformed, but no information about it
is lost — the residue map is a bijection. -/
def Reversible (t : Test D) : Prop := Function.Bijective (residue t)

/-- A **repeatable** test: re-running the test on the residual dish reproduces
the verdict. -/
def Repeatable (t : Test D) : Prop := ∀ d, verdict t (residue t d) = verdict t d

/-- A **destructive** test is one that is not nondestructive. -/
def Destructive (t : Test D) : Prop := ¬ Nondestructive t

/-- `t` **decides** the property `P` on dishes: its verdict is `true` exactly on
dishes satisfying `P`. -/
def Detects (t : Test D) (P : D → Prop) : Prop := ∀ d, verdict t d = true ↔ P d

/-! ## 3. The proved implications -/







/-! ## 4. Strictness of the hierarchy: two-dish counterexamples -/

/-- The **flip** test on `Bool`-dishes: always accepts, but swaps the dish.
Reversible and repeatable, yet destructive. -/
def flipTest : Test Bool := fun d => (true, !d)

/-- The **read-and-flip** test: reports the dish and swaps it.  Reversible,
destructive, and *not* repeatable — the second run contradicts the first. -/
def readFlipTest : Test Bool := fun d => (d, !d)

/-- The **burn** test: always accepts and reduces every dish to `false`.
Repeatable and destructive, but not reversible: the dish is irrecoverable. -/
def burnTest : Test Bool := fun _ => (true, false)










/-! ## 5. Sequential composition: the verification monoid -/

/-- Run `t₁`, then run `t₂` on the residual dish; the verdict is the conjunction
of the two verdicts. -/
def seq (t₁ t₂ : Test D) : Test D :=
  fun d => (verdict t₁ d && verdict t₂ (residue t₁ d), residue t₂ (residue t₁ d))

/-- The trivial certificate: accepts everything and touches nothing. -/
def one (D : Type*) : Test D := fun d => (true, d)













/-! ## 6. Counting: certificates are exponentially rare -/

variable (D)


/-- Certificates are exactly the `2^n` verdict functions: a nondestructive test
is precisely a predicate on dishes. -/
def nondestructiveEquiv : {t : Test D // Nondestructive t} ≃ (D → Bool) where
  toFun t := fun d => verdict t.1 d
  invFun f := ⟨fun d => (f d, d), fun _ => rfl⟩
  left_inv := by
    rintro ⟨t, ht⟩
    apply Subtype.ext
    exact ext_test (fun d => rfl) (fun d => (ht d).symm)
  right_inv := by intro f; rfl


/-- Reversible tests are exactly a verdict function together with a permutation
of the dishes. -/
noncomputable def reversibleEquiv : {t : Test D // Reversible t} ≃ (D → Bool) × Equiv.Perm D where
  toFun t := (fun d => verdict t.1 d, Equiv.ofBijective (residue t.1) t.2)
  invFun fs := ⟨fun d => (fs.1 d, fs.2 d), fs.2.bijective⟩
  left_inv := by
    rintro ⟨t, ht⟩
    exact Subtype.ext (ext_test (fun d => rfl) (fun d => rfl))
  right_inv := by
    rintro ⟨f, σ⟩
    exact Prod.ext rfl (Equiv.ext fun d => rfl)



end DestructiveVerification


