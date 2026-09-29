-- Prove2me | Definitions.Def_Applications_AntiMathematics_NonExtensional
-- name    : Applications_AntiMathematics_NonExtensional
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:31:54.775034+00:00
-- url     : https://prove2.me/theorems/6c977b4e-40f8-4c8c-ada4-1c3fd9e3025c
-- title:
--   Aether Catalog definitions — Applications_AntiMathematics_NonExtensional
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.AntiMathematics.NonExtensional`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/AntiMathematics/NonExtensional.lean by skeleton subtraction
import Mathlib

/-!
# Anti-Mathematics II: Negating the Axiom of Extensionality

**Mission.** *Anti-Mathematics: What if all axioms were negated?*  This file treats
the negation of the **Axiom of Extensionality**.

## The claim

Dropping (and negating) Extensionality yields a theory of **indistinguishable
sets**: distinct objects may have exactly the same members.  We build an explicit
model, `V = Option ℕ`, in which the Ackermann sets `some n` sit alongside a second,
distinct empty set `none`.  We prove:

* **Failure of Extensionality** (`non_extensionality`): `some 0` and `none` have the
  same (namely, no) members yet differ.
* Indistinguishability `Indist` is an **equivalence relation** (`indist_equiv`).
* Genuine sets are still faithfully separated (`indist_some`, `indist_none`).
* **The obstruction to quotienting** (`membership_not_congruent`): membership is
  *not* a congruence for indistinguishability, so one cannot naively collapse
  indistinguishables to recover an extensional universe.

This uses the Ackermann membership `Mem` of `AckermannModel.lean` (re-declared here
so the file is self-contained).
-/

namespace AntiMath

/-- Ackermann membership on `ℕ` (as in `AckermannModel.lean`). -/
def Mem (a b : ℕ) : Prop := b.testBit a


/-- A universe with a **duplicate empty set**: `none` is a second, distinct empty
set alongside the Ackermann empty `some 0`. -/
abbrev V := Option ℕ

/-- Membership in the non-extensional universe: `some m` belongs to `some n` iff
`m ∈ n` in the Ackermann sense; the atom `none` is never an element and has no
elements. -/
def NMem : V → V → Prop
  | some m, some n => Mem m n
  | _, _ => False

/-- **Indistinguishability**: two objects with exactly the same members. -/
def Indist (a b : V) : Prop := ∀ x, NMem x a ↔ NMem x b






end AntiMath


