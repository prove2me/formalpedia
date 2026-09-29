-- Prove2me | Definitions.Def_Novelty_ArgumentationStableGap
-- name    : Novelty_ArgumentationStableGap
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:02:08.988943+00:00
-- url     : https://prove2.me/theorems/407bed4d-ca02-4d76-a4c0-1460f5556907
-- title:
--   Aether Catalog definitions — Novelty_ArgumentationStableGap
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ArgumentationStableGap`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ArgumentationStableGap.lean by skeleton subtraction
import Mathlib

/-!
# The topology of argumentation, VI: the existence gap for stable extensions

This file is **self-contained** (it re-declares the basic Dung semantics) and
pursues, in *contrarian* mode, the **existence gap** left open by
`ArgumentationStable.lean`:

> Unlike preferred extensions, **stable extensions need not exist.**

We formulate four bold conjectures about the existence of stable extensions and
settle each one, proving two and disproving two.

## Bold conjectures, settled

* **`no_stable_cycle3`** — *Disproves* "every finite framework has a stable
  extension": the odd 3-cycle `0 → 1 → 2 → 0` has **no** stable extension.
* **`cycle3_preferred_not_stable`** — *Disproves* "every preferred extension is
  stable": in the 3-cycle the empty set is a preferred (indeed the unique
  admissible) extension, yet it is not stable.  So the strict inclusion
  `stable ⊊ preferred` of `ArgumentationStable.lean` is genuinely strict.
* **`stable_exists_of_finite_symmetric_irrefl`** — *Proves* "every finite
  symmetric irreflexive framework has a stable extension" (the existence gap
  closes on the symmetric side): a maximal conflict-free set exists by finiteness
  and is stable.
* **`no_stable_of_reflexive`** / **`no_stable_reflAF`** — *Disproves* "symmetry
  alone suffices for existence": a symmetric framework with a self-attack (hence
  reflexive) and at least one argument has no stable extension.  Irreflexivity in
  the previous item is therefore necessary.

Quantitatively, `stable_cycle3_ncard` records that the number of stable
extensions of the 3-cycle is `0`, in contrast with the count `n` for the
complete conflict graph (`ArgumentationStable.stable_completeAF_ncard`).
-/

namespace ArgStableGap

open Finset

variable {A : Type*} (R : A → A → Prop)

/-! ## Basic Dung semantics (self-contained) -/

/-- `S` is *conflict-free*: no argument in `S` attacks another in `S`. -/
def ConflictFree (S : Set A) : Prop := ∀ a ∈ S, ∀ b ∈ S, ¬ R a b

/-- `S` *defends* `a`: every attacker of `a` is counter-attacked from `S`. -/
def Defends (S : Set A) (a : A) : Prop := ∀ b, R b a → ∃ c ∈ S, R c b

/-- `S` is *admissible*: conflict-free and defends all its members. -/
def Admissible (S : Set A) : Prop := ConflictFree R S ∧ ∀ a ∈ S, Defends R S a

/-- `S` is a **preferred extension**: a maximal admissible set. -/
def Preferred (S : Set A) : Prop :=
  Admissible R S ∧ ∀ T, Admissible R T → S ⊆ T → T = S

/-- `S` is **maximal conflict-free**: a facet of the conflict-free complex. -/
def MaximalConflictFree (S : Set A) : Prop :=
  ConflictFree R S ∧ ∀ T, ConflictFree R T → S ⊆ T → T = S

/-- `S` is a **stable extension**: conflict-free and it attacks every argument it
does not contain. -/
def Stable (S : Set A) : Prop :=
  ConflictFree R S ∧ ∀ a, a ∉ S → ∃ b ∈ S, R b a

/-! ## The symmetric collapse (re-proved, self-contained) -/



/-! ## Positive existence: finite symmetric irreflexive frameworks -/



/-! ## Negative: reflexivity destroys existence -/


end ArgStableGap

/-! ## The odd 3-cycle: no stable extension -/

namespace ArgStableGap

open Finset

/-- The **3-cycle** framework `0 → 1 → 2 → 0` on `Fin 3`. -/
def cycle3 : Fin 3 → Fin 3 → Prop := fun a b => b = a + 1

instance : DecidableRel cycle3 := fun a b => by unfold cycle3; infer_instance





/-! ## The 3-cycle: a preferred extension that is not stable -/





/-! ## A concrete symmetric framework with no stable extension -/

/-- The single-argument framework with a self-attack: symmetric but reflexive. -/
def reflAF : Fin 1 → Fin 1 → Prop := fun _ _ => True




end ArgStableGap


