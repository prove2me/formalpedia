-- Prove2me | Definitions.Def_Applications_AntiMathematics_AntiFoundation
-- name    : Applications_AntiMathematics_AntiFoundation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:31:55.950126+00:00
-- url     : https://prove2.me/theorems/4f435521-30cc-4459-ac7c-d5e0d13c39a6
-- title:
--   Aether Catalog definitions — Applications_AntiMathematics_AntiFoundation
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.AntiMathematics.AntiFoundation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/AntiMathematics/AntiFoundation.lean by skeleton subtraction
import Mathlib

/-!
# Anti-Mathematics III: Negating the Axiom of Foundation

**Mission.** *Anti-Mathematics: What if all axioms were negated?*  This file treats
the negation of the **Axiom of Foundation (Regularity)**.

## The claim

In the pure Ackermann model of `AckermannModel.lean`, membership is well-founded
(`AckermannModel.foundation_wf`).  Negating Foundation means allowing a
**non-well-founded** membership — in the extreme, a *Quine atom* `Ω = {Ω}`, a set
that is its own unique element.  We build an explicit universe realising this:

  `W = Option ℕ`,   with the genuine Ackermann sets `some n` sitting alongside one
extra object `Ω = none` whose sole member is itself.

We prove, as a chain of fully verified results:

* `genuine_foundation` — on the genuine Ackermann sets membership is still
  well-founded (the contrast baseline);
* `omega_self_mem` — the Quine atom satisfies `Ω ∈ Ω`;
* `omega_mem_iff` — `Ω`'s only member is `Ω` (so `Ω = {Ω}`);
* `not_mem_self_genuine` — genuine sets never contain themselves;
* `regularity_fails` — the nonempty set `Ω` has **no** `∈`-minimal member, so the
  Axiom of Regularity fails;
* `anti_foundation` (main theorem) — membership in `W` is **not** well-founded.

The atom is still cleanly separated from the genuine sets (`omega_distinct`), so
this is a controlled failure of Foundation, not a collapse of the whole universe.
-/

namespace AntiMath

/-- Ackermann membership on `ℕ` (as in `AckermannModel.lean`). -/
def Mem (a b : ℕ) : Prop := b.testBit a



/-- The anti-founded universe: the genuine Ackermann sets `some n` together with a
single extra object `Ω = none`. -/
abbrev W := Option ℕ

/-- The **Quine atom** `Ω = {Ω}`. -/
def Omega : W := none

/-- Membership in the anti-founded universe.  Genuine sets `some m ∈ some n` behave
via Ackermann membership; the atom `Ω = none` has exactly one member, itself, and
belongs to nothing else. -/
def WMem : W → W → Prop
  | some m, some n => Mem m n
  | none, none => True
  | _, _ => False

@[inherit_doc] scoped infix:50 " ∈w " => WMem







end AntiMath


