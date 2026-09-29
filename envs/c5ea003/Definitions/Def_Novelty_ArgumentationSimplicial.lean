-- Prove2me | Definitions.Def_Novelty_ArgumentationSimplicial
-- name    : Novelty_ArgumentationSimplicial
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:02:09.338614+00:00
-- url     : https://prove2.me/theorems/10dadd3c-fa5b-49a0-844a-25c0acf2989d
-- title:
--   Aether Catalog definitions — Novelty_ArgumentationSimplicial
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ArgumentationSimplicial`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ArgumentationSimplicial.lean by skeleton subtraction
import Mathlib

/-!
# The topology of argumentation, III: the simplicial complex `K(AF)` and its Euler characteristic

This file is **self-contained**.  It makes precise the central geometric claim
about argumentation frameworks and settles the associated Euler-characteristic
conjecture.

## The complex `K(AF)`

For an argumentation framework `(A, R)` the *conflict-free* subsets of `A` are
**downward closed**: any subset of a conflict-free set is conflict-free.  This is
exactly the defining axiom of an *abstract simplicial complex*.  We record this
as `conflictFreeComplex R : ASC A`.  (Note: it is the **conflict-free sets**, not
the preferred extensions, that form the complex — preferred extensions are the
*maximal* admissible sets and are not downward closed, so the naive reading of
the informal conjecture does not typecheck; `conflictFreeComplex` is the correct
carrier of the topology.)

## Euler characteristic

`eulerChar F` is the (unreduced) Euler characteristic of a finite family of
faces, `∑_{∅ ≠ s ∈ F} (-1)^(dim s)` with `dim s = |s| - 1`.  We prove
`eulerChar_powerset`: the full simplex on a nonempty vertex set is contractible
(`χ = 1`), and empty otherwise.

## The Euler = semantics conjecture is false

The informal conjecture asserts

  `χ(K(AF)) = |preferred extensions| − |grounded extension|`.

We refute it with an explicit witness: the attack-free framework on a single
argument (`R0` on `Fin 1`).  There `χ(K) = 1` (a point), there is exactly one
preferred extension, and the grounded extension has size `1`, so the right-hand
side is `1 − 1 = 0 ≠ 1`.  See `euler_semantics_conjecture_false`.
-/

namespace ArgTop

open Finset

variable {A : Type*}

/-- `S` is conflict-free: no argument in `S` attacks another in `S`. -/
def ConflictFree (R : A → A → Prop) (S : Set A) : Prop := ∀ a ∈ S, ∀ b ∈ S, ¬ R a b

/-- Conflict-free sets are downward closed. -/
theorem conflictFree_subset (R : A → A → Prop) {S T : Set A} (h : S ⊆ T)
    (hT : ConflictFree R T) : ConflictFree R S :=
  fun a ha b hb => hT a (h ha) b (h hb)

/-- An **abstract simplicial complex** on a vertex type `V`: a downward-closed
family of finite *faces*. -/
structure ASC (V : Type*) where
  /-- The set of faces (simplices) of the complex. -/
  faces : Set (Finset V)
  /-- The faces are downward closed: any subset of a face is a face. -/
  downClosed : ∀ ⦃s⦄, s ∈ faces → ∀ ⦃t⦄, t ⊆ s → t ∈ faces

/-- **`K(AF)`: the conflict-free subsets of an argumentation framework form an
abstract simplicial complex** on the vertex set of arguments. -/
def conflictFreeComplex (R : A → A → Prop) : ASC A where
  faces := {s : Finset A | ConflictFree R (↑s : Set A)}
  downClosed := by
    intro s hs t hts
    exact conflictFree_subset R (Finset.coe_subset.mpr hts) hs



/-- (Unreduced) **Euler characteristic** of a finite family of faces:
`∑_{∅ ≠ s ∈ F} (-1)^(dim s)` where the dimension of `s` is `|s| - 1`. -/
def eulerChar [DecidableEq A] (F : Finset (Finset A)) : ℤ :=
  ∑ s ∈ F, if s = ∅ then 0 else (-1) ^ (s.card - 1)


open Classical in
/-- The finite face set of `K(AF)` for a finite framework. -/
noncomputable def facesFinset [Fintype A] (R : A → A → Prop) : Finset (Finset A) :=
  Finset.univ.filter (fun s => ConflictFree R (↑s : Set A))

/-!
## Refuting the Euler = semantics conjecture

We now set up the machinery needed to state the conjecture (`Defends`,
`Admissible`, `Preferred`, `groundedExt`) and produce the explicit
counterexample.
-/

/-- `S` defends `a`: every attacker of `a` is counter-attacked from `S`. -/
def Defends (R : A → A → Prop) (S : Set A) (a : A) : Prop :=
  ∀ b, R b a → ∃ c ∈ S, R c b

/-- `S` is admissible: conflict-free and defends all its members. -/
def Admissible (R : A → A → Prop) (S : Set A) : Prop :=
  ConflictFree R S ∧ ∀ a ∈ S, Defends R S a

/-- The characteristic (defense) operator. -/
def charF (R : A → A → Prop) (S : Set A) : Set A := {a | Defends R S a}

/-- `S` is a preferred extension: a maximal admissible set. -/
def Preferred (R : A → A → Prop) (S : Set A) : Prop :=
  Admissible R S ∧ ∀ T, Admissible R T → S ⊆ T → T = S

theorem charF_mono (R : A → A → Prop) {S T : Set A} (h : S ⊆ T) :
    charF R S ⊆ charF R T := by
  intro a ha b hb; obtain ⟨c, hc, hcb⟩ := ha b hb; exact ⟨c, h hc, hcb⟩

/-- The defense operator as a monotone self-map of `Set A`. -/
def charFHom (R : A → A → Prop) : Set A →o Set A := ⟨charF R, fun _ _ h => charF_mono R h⟩

/-- The grounded extension: least fixed point of the defense operator. -/
noncomputable def groundedExt (R : A → A → Prop) : Set A := OrderHom.lfp (charFHom R)


/-- The attack-free framework on a single argument. -/
def R0 : Fin 1 → Fin 1 → Prop := fun _ _ => False









end ArgTop


