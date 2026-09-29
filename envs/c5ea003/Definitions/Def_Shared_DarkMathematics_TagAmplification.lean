-- Prove2me | Definitions.Def_Shared_DarkMathematics_TagAmplification
-- name    : Shared_DarkMathematics_TagAmplification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:35:39.270458+00:00
-- url     : https://prove2.me/theorems/d69175ca-ccfb-461e-bb87-3e8976944d7e
-- title:
--   Aether Catalog definitions — Shared_DarkMathematics_TagAmplification
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.DarkMathematics.TagAmplification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/DarkMathematics/TagAmplification.lean by skeleton subtraction
import Mathlib

/-!
# Dark existence and finite tag amplification

This file isolates a precise structural obstruction to treating “darkness level” as an
intrinsic hierarchy.  Provability is intentionally a parameter: no soundness or consistency
assumption is hidden in the definitions.

A predicate is dark when the proof system proves that it has a witness, while proving none
of the instances selected by a naming map.  `AtLeast k P` says that `P` has at least `k`
distinct witnesses.

The main result, `dark_all_finite_levels`, shows that one dark existential can be amplified
to every positive finite level merely by adjoining a finite, mathematically irrelevant tag.
The only assumptions on provability are the two elementary syntactic transformations needed
for this coding: existential tag introduction and tag erasure for instances.  Consequently,
raw witness cardinality cannot support a strict “hardness” hierarchy without an additional
invariance requirement forbidding such definitional/tag extensions.
-/

namespace DarkMathematics

/-- There are at least `k` distinct values satisfying `P`. -/
def AtLeast {α : Type*} (k : ℕ) (P : α → Prop) : Prop :=
  ∃ s : Finset α, s.card = k ∧ ∀ x ∈ s, P x

/-- Darkness relative to a proof predicate and a chosen sequence of named objects. -/
def Dark {α : Type*} (Prov : Prop → Prop) (name : ℕ → α) (P : α → Prop) : Prop :=
  Prov (∃ x, P x) ∧ ∀ n, ¬ Prov (P (name n))

/-- Level-`k` darkness: provable existence of `k` distinct witnesses, but no named instance
is provable. -/
def DarkLevel {α : Type*} (Prov : Prop → Prop) (name : ℕ → α)
    (k : ℕ) (P : α → Prop) : Prop :=
  Prov (AtLeast k P) ∧ ∀ n, ¬ Prov (P (name n))

/-- Add one of `k+1` finite tags to every named object. -/
def taggedName {α : Type*} (k : ℕ) (name : ℕ → α) (n : ℕ) : Fin (k + 1) × α :=
  (⟨n % (k + 1), Nat.mod_lt n (Nat.succ_pos k)⟩, name (n / (k + 1)))

/-
The tagged naming map reaches every finite tag over every named payload.
-/


/-
The tagged predicate has a witness exactly when the original predicate does.
-/


