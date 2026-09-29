-- Prove2me | Definitions.Def_Novelty_ArgumentationStable
-- name    : Novelty_ArgumentationStable
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-14T01:17:25.389917+00:00
-- url     : https://prove2.me/theorems/04e4887e-8a7f-4a4c-87ab-60de4bdbc18f
-- title:
--   Aether Catalog definitions — Novelty_ArgumentationStable
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ArgumentationStable`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ArgumentationStable.lean by skeleton subtraction
import Mathlib

/-!
# The topology of argumentation, V: stable extensions and the stable/preferred/Euler chain

This file is **self-contained** (it re-declares the basic Dung semantics) and
deepens the theory begun in `ArgumentationCore`, `ArgumentationExtensions`,
`ArgumentationSimplicial` and `ArgumentationSymmetric` by developing the
strongest of the classical *extension-based* semantics — the **stable
extension** — and situating it inside the full hierarchy

  `stable ⟹ preferred ⟹ complete ⟹ admissible ⟹ conflict-free`.

A set `S` is a **stable extension** when it is conflict-free and *attacks every
argument it does not contain* (`∀ a ∉ S, ∃ b ∈ S, R b a`).  Stable extensions are
the "no abstention" positions: every argument is either accepted or explicitly
defeated.

## The chain of results

* `stable_defends`     — a stable set defends each of its members;
* `stable_admissible`  — every stable extension is admissible;
* `stable_complete`    — every stable extension is complete (closed under defense);
* `stable_preferred`   — **every stable extension is preferred** (maximal admissible);
* `stable_maximalConflictFree` — every stable extension is a *facet* of `K(AF)`;
* `groundedExt_subset_stable` — the grounded extension is contained in every
  stable extension (skeptical ⊆ every stable position).

## The symmetric bridge and the Euler correspondence

For **symmetric irreflexive** frameworks (the model of two-sided disagreement)
we prove the exact collapse

* `maximalConflictFree_stable_of_symmetric` and hence
* `stable_iff_preferred_of_symmetric_irrefl` — **stable = preferred = facet** of
  the conflict-free complex `K(AF)`.

Specialising to the **complete conflict graph** `completeAF n` (which is
symmetric and irreflexive) we obtain, entirely self-contained:

* `stable_completeAF_iff` — the stable extensions are exactly the singletons;
* `stable_completeAF_ncard` — there are exactly `n` of them;
* `euler_eq_stable_completeAF` — **the Euler characteristic of `K(AF)` equals the
  number of stable extensions** (for `n ≥ 1`), extending the Euler/semantics
  bridge of `ArgumentationSymmetric` from preferred to stable extensions.
-/

namespace ArgTop

open Finset

variable {A : Type*} (R : A → A → Prop)

/-! ## Basic Dung semantics (self-contained) -/

/-- `S` is *conflict-free*: no argument in `S` attacks another in `S`. -/
def ConflictFree (S : Set A) : Prop := ∀ a ∈ S, ∀ b ∈ S, ¬ R a b

/-- `S` *defends* `a`: every attacker of `a` is counter-attacked from `S`. -/
def Defends (S : Set A) (a : A) : Prop := ∀ b, R b a → ∃ c ∈ S, R c b

/-- `S` is *admissible*: conflict-free and defends all its members. -/
def Admissible (S : Set A) : Prop := ConflictFree R S ∧ ∀ a ∈ S, Defends R S a

/-- The *characteristic (defense) operator*. -/
def charF (S : Set A) : Set A := {a | Defends R S a}

/-- `S` is a **complete extension**: admissible and closed under defense. -/
def Complete (S : Set A) : Prop := Admissible R S ∧ charF R S ⊆ S

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

theorem defends_mono {S T : Set A} (h : S ⊆ T) {a : A} (ha : Defends R S a) :
    Defends R T a := by
  intro b hb
  obtain ⟨c, hc, hcb⟩ := ha b hb
  exact ⟨c, h hc, hcb⟩

theorem charF_mono {S T : Set A} (h : S ⊆ T) : charF R S ⊆ charF R T :=
  fun _ ha => defends_mono R h ha

/-! ## The stable hierarchy -/






/-! ## The grounded extension is below every stable extension -/

/-- The defense operator as a monotone self-map of `Set A`. -/
def charFHom : Set A →o Set A := ⟨charF R, fun _ _ h => charF_mono R h⟩

/-- The **grounded extension**: least fixed point of the defense operator. -/
noncomputable def groundedExt : Set A := OrderHom.lfp (charFHom R)



/-! ## Symmetric frameworks: stable = preferred = facet -/






end ArgTop

/-! ## The complete conflict graph: stable count and the Euler bridge -/

namespace ArgTop

open Finset

/-- The **complete conflict graph** on `n` arguments: every two distinct
arguments attack each other. -/
def completeAF (n : ℕ) : Fin n → Fin n → Prop := fun a b => a ≠ b






/-! ### Euler characteristic -/

/-- (Unreduced) **Euler characteristic** of a finite family of faces. -/
def eulerChar {A : Type*} [DecidableEq A] (F : Finset (Finset A)) : ℤ :=
  ∑ s ∈ F, if s = ∅ then 0 else (-1) ^ (s.card - 1)

open Classical in
/-- The finite face set of `K(AF)` for a finite framework. -/
noncomputable def facesFinset {A : Type*} [Fintype A] (R : A → A → Prop) : Finset (Finset A) :=
  Finset.univ.filter (fun s => ConflictFree R (↑s : Set A))




end ArgTop


