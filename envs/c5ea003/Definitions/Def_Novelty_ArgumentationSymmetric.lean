-- Prove2me | Definitions.Def_Novelty_ArgumentationSymmetric
-- name    : Novelty_ArgumentationSymmetric
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:02:09.01319+00:00
-- url     : https://prove2.me/theorems/c1c2fe76-c7ba-4b2a-a6c9-d6aa99eb25dd
-- title:
--   Aether Catalog definitions — Novelty_ArgumentationSymmetric
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ArgumentationSymmetric`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ArgumentationSymmetric.lean by skeleton subtraction
import Mathlib

/-!
# The topology of argumentation, IV: symmetric frameworks, naive extensions, and the Euler bridge

This file continues the study of the *conflict-free complex* `K(AF)` of a Dung
argumentation framework `(A, R)` begun in `ArgumentationCore`.  It isolates the
class of **symmetric** frameworks — those where attacks come in pairs
(`R a b → R b a`), the natural setting for mutual disagreement — and establishes
the precise dictionary between the *semantics* of the framework and the
*combinatorial topology* of its complex.

## Main results

* `conflictFree_admissible_of_symmetric` — in a symmetric framework every
  conflict-free set is admissible: each argument defends *itself*, because an
  attacker is always attacked back.  Hence `admissible_iff_conflictFree_of_symmetric`.
* `preferred_iff_maximalConflictFree_of_symmetric` — the **preferred extensions
  of a symmetric framework are exactly the maximal conflict-free sets**, i.e. the
  *facets* of the complex `K(AF)` (its inclusion-maximal faces).  This is the
  key identification of a *semantic* notion (preferred = maximal credulous
  position) with a *topological* one (facet of the independence complex).
* `groundedExt_eq_unattacked_of_symmetric` — the grounded (skeptical) extension
  of a symmetric framework is precisely the set of *unattacked* arguments, the
  isolated vertices of the conflict graph.

## The complete conflict graph and the Euler bridge

For the **complete conflict graph** `completeAF n` on `n` arguments (every two
distinct arguments attack each other), the complex `K(AF)` is `n` isolated
points.  We prove:

* `conflictFree_completeAF_iff` — conflict-free = subsingleton;
* `preferred_completeAF_iff` — preferred extensions are exactly the singletons;
* `preferred_completeAF_ncard` — there are exactly `n` of them;
* `euler_completeAF` — the Euler characteristic of `K(AF)` equals `n`;
* `euler_eq_preferred_completeAF` — **the Euler characteristic equals the number
  of preferred extensions** (for `n ≥ 1`).

This is the *correct* Euler/semantics bridge: the naive identity refuted in
`ArgumentationSimplicial` is replaced, on the symmetric side, by an exact match
between `χ(K(AF))` and the count of maximal independent sets.  The hypothesis
`n ≥ 1` is sharp — see the boundary remark `euler_ne_preferred_completeAF_zero`.
-/

namespace ArgTop

open Finset

variable {A : Type*} {R : A → A → Prop}

/-! ## Basic Dung semantics (self-contained)

We re-declare the core notions of the conflict-free complex so that this file
compiles independently. -/

/-- `S` is *conflict-free*: no argument in `S` attacks another in `S`. -/
def ConflictFree (R : A → A → Prop) (S : Set A) : Prop := ∀ a ∈ S, ∀ b ∈ S, ¬ R a b

/-- `S` *defends* `a`: every attacker of `a` is counter-attacked from `S`. -/
def Defends (R : A → A → Prop) (S : Set A) (a : A) : Prop := ∀ b, R b a → ∃ c ∈ S, R c b

/-- `S` is *admissible*: conflict-free and defends all its members. -/
def Admissible (R : A → A → Prop) (S : Set A) : Prop :=
  ConflictFree R S ∧ ∀ a ∈ S, Defends R S a

/-- The *characteristic (defense) operator*. -/
def charF (R : A → A → Prop) (S : Set A) : Set A := {a | Defends R S a}

/-- The defense operator is monotone. -/
theorem charF_mono (R : A → A → Prop) {S T : Set A} (h : S ⊆ T) : charF R S ⊆ charF R T := by
  intro a ha b hb; obtain ⟨c, hc, hcb⟩ := ha b hb; exact ⟨c, h hc, hcb⟩


/-! ## Symmetric frameworks: conflict-free = admissible -/




/-! ## Preferred extensions and grounded extension of a symmetric framework -/

/-- `S` is a **preferred extension**: a maximal admissible set. -/
def Preferred (R : A → A → Prop) (S : Set A) : Prop :=
  Admissible R S ∧ ∀ T, Admissible R T → S ⊆ T → T = S

/-- `S` is **maximal conflict-free**: a facet of the conflict-free complex. -/
def MaximalConflictFree (R : A → A → Prop) (S : Set A) : Prop :=
  ConflictFree R S ∧ ∀ T, ConflictFree R T → S ⊆ T → T = S


/-- The defense operator as a monotone self-map of `Set A`. -/
def charFHom (R : A → A → Prop) : Set A →o Set A := ⟨charF R, fun _ _ h => charF_mono R h⟩

/-- The **grounded extension**: least fixed point of the defense operator. -/
noncomputable def groundedExt (R : A → A → Prop) : Set A := OrderHom.lfp (charFHom R)



/-! ## The complete conflict graph -/

/-- The **complete conflict graph** on `n` arguments: every two *distinct*
arguments attack each other. -/
def completeAF (n : ℕ) : Fin n → Fin n → Prop := fun a b => a ≠ b






/-! ## Euler characteristic of the complete conflict graph -/

/-- (Unreduced) **Euler characteristic** of a finite family of faces:
`∑_{∅ ≠ s ∈ F} (-1)^(dim s)` where the dimension of `s` is `|s| - 1`. -/
def eulerChar [DecidableEq A] (F : Finset (Finset A)) : ℤ :=
  ∑ s ∈ F, if s = ∅ then 0 else (-1) ^ (s.card - 1)

open Classical in
/-- The finite face set of `K(AF)` for a finite framework. -/
noncomputable def facesFinset [Fintype A] (R : A → A → Prop) : Finset (Finset A) :=
  Finset.univ.filter (fun s => ConflictFree R (↑s : Set A))


/-
**The Euler characteristic of the complete conflict graph on `n` arguments
is `n`** — the complex is `n` isolated points.
-/


/-! ## Boundary case: the empty framework -/

/-
**Boundary remark.**  The Euler bridge is sharp: for the *empty* framework
(`n = 0`) the complex `K(AF)` is a single point (the empty face), so its Euler
characteristic is `0`, yet there is exactly one preferred extension (the empty
set).  Thus `χ ≠ #preferred` at `n = 0`, and the hypothesis `n ≥ 1` cannot be
dropped.
-/

/-! ## Examples and sanity checks -/

/-!
-- !-- Lab Notes -- !--

**Hypothesis.**  In the general (asymmetric) theory the naive identity
`χ(K(AF)) = |preferred| − |grounded|` is false.  We conjectured that on the
*symmetric* side — where attacks are mutual, the natural model of two-sided
disagreement — a clean bridge survives: the preferred extensions should coincide
with the facets (maximal faces) of the conflict-free complex, and for the
complete conflict graph the Euler characteristic should count them exactly.

**Experiment.**  We proved, with no extra hypotheses beyond symmetry, that
conflict-free = admissible (`conflictFree_admissible_of_symmetric`) — each
argument defends *itself* because any attacker is attacked back.  This collapses
preferred extensions onto maximal conflict-free sets
(`preferred_iff_maximalConflictFree_of_symmetric`), i.e. the facets of `K(AF)`,
and pins the grounded extension to the isolated vertices
(`groundedExt_eq_unattacked_of_symmetric`).  For the complete conflict graph the
complex is `n` isolated points, with exactly `n` preferred extensions
(`preferred_completeAF_ncard`) and Euler characteristic `n`
(`euler_completeAF`), yielding the exact bridge `euler_eq_preferred_completeAF`.

**Analysis.**  The symmetric self-defense phenomenon is what makes semantics and
topology agree: admissibility, the obstruction to reading extensions off the
complex in the general case, becomes free.  The bridge `χ = |preferred|` is thus
a theorem about *independence complexes of the mutual-attack graph*, not about
Dung frameworks in general.

**Critique.**  The bridge is sharp: at `n = 0` the complex is a single (empty)
point with `χ = 0`, yet there is one preferred extension, so `χ ≠ |preferred|`.
This boundary is recorded as `euler_ne_preferred_completeAF_zero`, and the
hypothesis `0 < n` in the bridge cannot be dropped.  None of the results are
vacuous: each uses genuine structural input (self-defense, maximality, an
injective enumeration of singletons, an alternating-sum computation).

**Synthesis.**  The correct Euler/semantics correspondence for symmetric
frameworks is: *preferred extensions = facets of `K(AF)`*, and for the complete
conflict graph the alternating face count equals the number of maximal
independent sets.  See `FUTURE_DIRECTIONS.md` for the conjectural extension to
arbitrary symmetric irreflexive frameworks and to full homology.
-/

end ArgTop


