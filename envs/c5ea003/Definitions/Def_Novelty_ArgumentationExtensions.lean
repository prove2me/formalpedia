-- Prove2me | Definitions.Def_Novelty_ArgumentationExtensions
-- name    : Novelty_ArgumentationExtensions
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:01:53.619162+00:00
-- url     : https://prove2.me/theorems/b2e87297-db71-4bd9-b7f1-f8caf20a0113
-- title:
--   Aether Catalog definitions — Novelty_ArgumentationExtensions
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ArgumentationExtensions`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ArgumentationExtensions.lean by skeleton subtraction
import Mathlib

/-!
# The topology of argumentation, II: preferred and grounded extensions

This file is **self-contained** (it re-declares the basic Dung semantics from
`ArgumentationCore`) and develops the two central *extension-based* semantics of
an argumentation framework `(A, R)`:

* `Preferred S` — `S` is a **preferred extension**: a *maximal* admissible set.
* `Complete S`  — `S` is a **complete extension**: admissible and closed under
  the defense operator (`charF S ⊆ S`).
* `groundedExt` — the **grounded extension**: the *least* fixed point of the
  defense operator (skeptical semantics).

Main results:

* `admissible_sUnion_chain`   — admissible sets are closed under unions of chains.
* `exists_preferred_superset` — (Zorn) every admissible set extends to a
  preferred extension; in particular `exists_preferred`.
* `preferred_complete`        — **every preferred extension is complete**
  (Dung); the proof is a direct application of the Fundamental Lemma.
* `groundedExt_subset_complete` / `groundedExt_subset_preferred` — the grounded
  extension is contained in every complete, hence every preferred, extension:
  the skeptically-accepted arguments are accepted under every credulous position.
-/

namespace ArgTop

variable {A : Type*} (R : A → A → Prop)

/-- `S` is conflict-free: no argument in `S` attacks another in `S`. -/
def ConflictFree (S : Set A) : Prop := ∀ a ∈ S, ∀ b ∈ S, ¬ R a b

/-- `S` defends `a`: every attacker of `a` is counter-attacked from `S`. -/
def Defends (S : Set A) (a : A) : Prop := ∀ b, R b a → ∃ c ∈ S, R c b

/-- `S` is admissible: conflict-free and defends all its members. -/
def Admissible (S : Set A) : Prop := ConflictFree R S ∧ ∀ a ∈ S, Defends R S a

/-- The characteristic (defense) operator. -/
def charF (S : Set A) : Set A := {a | Defends R S a}

/-- `S` is a **complete extension**: admissible and closed under defense. -/
def Complete (S : Set A) : Prop := Admissible R S ∧ charF R S ⊆ S

/-- `S` is a **preferred extension**: a maximal admissible set. -/
def Preferred (S : Set A) : Prop :=
  Admissible R S ∧ ∀ T, Admissible R T → S ⊆ T → T = S

theorem defends_mono {S T : Set A} (h : S ⊆ T) {a : A} (ha : Defends R S a) :
    Defends R T a := by
  intro b hb
  obtain ⟨c, hc, hcb⟩ := ha b hb
  exact ⟨c, h hc, hcb⟩

theorem charF_mono {S T : Set A} (h : S ⊆ T) : charF R S ⊆ charF R T :=
  fun _ ha => defends_mono R h ha







/-- The defense operator as a monotone self-map of the complete lattice `Set A`. -/
def charFHom : Set A →o Set A := ⟨charF R, fun _ _ h => charF_mono R h⟩

/-- The **grounded extension**: the least fixed point of the defense operator. -/
noncomputable def groundedExt : Set A := OrderHom.lfp (charFHom R)





end ArgTop


