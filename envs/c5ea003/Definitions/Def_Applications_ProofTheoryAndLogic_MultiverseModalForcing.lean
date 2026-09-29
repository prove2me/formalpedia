-- Prove2me | Definitions.Def_Applications_ProofTheoryAndLogic_MultiverseModalForcing
-- name    : Applications_ProofTheoryAndLogic_MultiverseModalForcing
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:25.033786+00:00
-- url     : https://prove2.me/theorems/7c7e6ce3-55be-4ac2-a24d-395e9c35acb7
-- title:
--   Aether Catalog definitions — Applications_ProofTheoryAndLogic_MultiverseModalForcing
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ProofTheoryAndLogic.MultiverseModalForcing`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ProofTheoryAndLogic/MultiverseModalForcing.lean by skeleton subtraction
import Mathlib
/-
# The Modal Logic of Forcing — a Kripke-semantic deepening of Multiverse Set Theory

This file equips the combinatorial core of the set-theoretic *multiverse* with a
**modal structure of forcing**, following the Hamkins–Löwe programme:

* **possibility** `◇p` — `p` holds in *some* forcing (generic) extension;
* **necessity**  `□p` — `p` holds in *every* forcing extension.

Forcing extensions form a Kripke *frame*: an accessibility relation `R` on worlds
(models of set theory).  We give the standard Kripke semantics for a language of
modal set-theoretic sentences and prove that the forcing frame is **sound for the
modal system `S4.2`**, the theorem at the heart of the modal logic of forcing:

* `sound_K`      — the distribution axiom `□(p → q) → (□p → □q)` (any frame);
* `sound_Nec`    — the necessitation rule (any frame);
* `sound_T`      — `□p → p` from **reflexivity** of forcing (you force over yourself);
* `sound_Four`   — `□p → □□p` from **transitivity** (iterated forcing);
* `sound_Two`    — `◇□p → □◇p` from **directedness** (any two extensions have a
  common further extension — the amalgamation/product-forcing property).

Together `K, T, 4, .2` axiomatise `S4.2`.  We also prove the **duality**
`◇p ↔ ¬□¬p`, monotonicity and distribution laws, package the result as
`forcing_sound_S42`, instantiate the abstract frame with a concrete
*flip-reachability* forcing frame over the multiverse, and finally show the logic
is **properly weaker than `S5`**: the characteristic axiom `B : p → □◇p` **fails**
in a directed reflexive-transitive forcing frame (`B_fails`).  Thus forcing is
genuinely `S4.2` and not `S5` — you cannot, in general, force your way back.

Everything is proved from first principles over `Mathlib`, self-contained.
-/

namespace MultiverseModalForcing

open Classical

/-! ## Worlds and modal sentences -/

/-- A `World` (a model of the ambient set theory) is a truth assignment to atoms. -/
abbrev World (α : Type*) := α → Bool

/-- A **multiverse** is a collection of worlds. -/
abbrev Multiverse (α : Type*) := Set (World α)

/-- Modal propositional set-theoretic sentences over atoms `α`, with a `box`
    (necessity / "holds in every forcing extension") modality. -/
inductive MSentence (α : Type*) where
  | atom : α → MSentence α
  | tru : MSentence α
  | fls : MSentence α
  | neg : MSentence α → MSentence α
  | conj : MSentence α → MSentence α → MSentence α
  | disj : MSentence α → MSentence α → MSentence α
  | imp : MSentence α → MSentence α → MSentence α
  | box : MSentence α → MSentence α
  deriving DecidableEq

namespace MSentence

/-- Diamond (possibility): `◇p := ¬□¬p` — `p` holds in *some* forcing extension. -/
def dia {α} (p : MSentence α) : MSentence α := .neg (.box (.neg p))

end MSentence

/-! ## Kripke semantics for forcing

`R w v` reads "`v` is a forcing extension of `w`".  `M` is the multiverse of
admissible worlds.  `meval R M w p` is the truth of `p` at world `w`. -/

/-- Kripke evaluation of a modal sentence at a world, relative to an accessibility
    relation `R` (the forcing-extension relation) and a multiverse `M`. -/
def meval {α} (R : World α → World α → Prop) (M : Multiverse α) (w : World α) :
    MSentence α → Prop
  | .atom a => w a = true
  | .tru => True
  | .fls => False
  | .neg p => ¬ meval R M w p
  | .conj p q => meval R M w p ∧ meval R M w q
  | .disj p q => meval R M w p ∨ meval R M w q
  | .imp p q => meval R M w p → meval R M w q
  | .box p => ∀ v, R w v → v ∈ M → meval R M v p

/-- A modal sentence is **valid** in the frame `(R, M)` if it is true at every
    admissible world. -/
def MValid {α} (R : World α → World α → Prop) (M : Multiverse α) (p : MSentence α) : Prop :=
  ∀ w ∈ M, meval R M w p







/-! ## Duality between necessity and possibility -/



/-! ## Soundness of the modal system S4.2 for forcing frames

We isolate the three frame conditions that forcing satisfies and show each
validates the corresponding modal axiom. -/

/-- **Reflexivity** of forcing on `M`: every admissible world is a (trivial)
    forcing extension of itself. -/
def Reflexive {α} (R : World α → World α → Prop) (M : Multiverse α) : Prop :=
  ∀ w ∈ M, R w w

/-- **Transitivity** of forcing: a forcing extension of a forcing extension is a
    forcing extension (iterated forcing). -/
def Transitive {α} (R : World α → World α → Prop) : Prop :=
  ∀ w v u, R w v → R v u → R w u

/-- **Directedness** of forcing: any two forcing extensions of a world have a
    common further extension (amalgamation / product forcing). -/
def Directed {α} (R : World α → World α → Prop) (M : Multiverse α) : Prop :=
  ∀ w ∈ M, ∀ v₁ v₂, R w v₁ → v₁ ∈ M → R w v₂ → v₂ ∈ M →
    ∃ u ∈ M, R v₁ u ∧ R v₂ u






/-! ## Derived modal principles -/






/-! ## Packaging the S4.2 soundness theorem -/

/-- A **forcing frame** on a multiverse `M`: an accessibility relation that is
    reflexive, transitive and directed — the abstract multiverse axioms for
    forcing extensions. -/
structure ForcingFrame (α : Type*) where
  /-- The forcing-extension accessibility relation. -/
  R : World α → World α → Prop
  /-- The multiverse of admissible worlds. -/
  M : Multiverse α
  refl : Reflexive R M
  trans : Transitive R
  dir : Directed R M


/-! ## A concrete forcing frame: flip-reachability

We model a generic extension deciding an atom the other way by *flipping* its
truth value.  Two worlds are mutually accessible when they differ on only
finitely many atoms — the reachable class under finitely many forcing steps. -/

/-- The flip-reachability relation: `v` differs from `w` on a finite set of atoms.
    This is the equivalence class of worlds reachable by finitely many single-atom
    forcing steps. -/
def FlipReach {α} [DecidableEq α] (w v : World α) : Prop :=
  ∃ s : Finset α, ∀ x, v x = if x ∈ s then !(w x) else w x

theorem FlipReach.refl {α} [DecidableEq α] (w : World α) : FlipReach w w :=
  ⟨∅, by intro x; simp⟩

theorem FlipReach.symm {α} [DecidableEq α] {w v : World α}
    (h : FlipReach w v) : FlipReach v w := by
  obtain ⟨s, hs⟩ := h
  refine ⟨s, ?_⟩
  intro x
  by_cases hx : x ∈ s <;> simp [hs x, hx]

theorem FlipReach.trans {α} [DecidableEq α] {w v u : World α}
    (h1 : FlipReach w v) (h2 : FlipReach v u) : FlipReach w u := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  refine ⟨symmDiff s t, ?_⟩
  intro x
  rw [ht x, hs x]
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;>
    simp [Finset.mem_symmDiff, hxs, hxt]

/-- The **flip-reachability forcing frame** over a multiverse closed under
    flip-reachability.  Concretely we take the *full* multiverse, which is closed
    under all finite flips.  This realises the abstract forcing frame, so it too
    validates `S4.2`. -/
def flipFrame (α : Type*) [DecidableEq α] : ForcingFrame α where
  R := FlipReach
  M := Set.univ
  refl := fun w _ => FlipReach.refl w
  trans := fun _ _ _ h1 h2 => FlipReach.trans h1 h2
  dir := by
    intro w _ v₁ v₂ h1 _ h2 _
    exact ⟨v₁, trivial, FlipReach.refl v₁, (h1.symm.trans h2).symm⟩


/-! ## Properness: forcing is `S4.2`, not `S5`

The characteristic `S5` axiom `B : p → □◇p` fails in a directed reflexive
transitive forcing frame.  Hence the modal logic of forcing is *properly* weaker
than `S5`: from a generic extension you cannot in general force *back* to the
ground model. -/

/-- A two-world forcing frame over a single atom.  `wT` (atom true) can force to
    `wF` (atom false), but `wF` is a *sink*: no forcing extension of `wF` makes
    the atom true again.  This is reflexive, transitive and directed. -/
def wT : World Bool := fun _ => true
def wF : World Bool := fun _ => false

/-- Sink accessibility: from any world you may force to `wF`, and forcing is
    reflexive.  `wF` has no extension other than itself. -/
def sinkR (x y : World Bool) : Prop := y = wF ∨ x = y

theorem sinkR_refl : Reflexive sinkR Set.univ := fun _ _ => Or.inr rfl

theorem sinkR_trans : Transitive sinkR := by
  intro x y z hxy hyz
  rcases hyz with h | h
  · exact Or.inl h
  · subst h; exact hxy

theorem sinkR_dir : Directed sinkR Set.univ := by
  intro w _ v₁ v₂ _ _ _ _
  exact ⟨wF, trivial, Or.inl rfl, Or.inl rfl⟩

/-- The sink frame is a genuine forcing frame (reflexive, transitive, directed). -/
def sinkFrame : ForcingFrame Bool where
  R := sinkR
  M := Set.univ
  refl := sinkR_refl
  trans := sinkR_trans
  dir := sinkR_dir



/-! ## Independence recast modally

The multiverse notion of *independence* (true in some world, false in another)
is exactly modal *contingency* `◇p ∧ ◇¬p` under the full-accessibility frame.  We
record the modal reading and a concrete instance. -/

/-- Three atomic set-theoretic assertions, as in the base multiverse file. -/
inductive Claim
  | CH | VeqL | Meas
  deriving DecidableEq, Fintype

open Claim

/-- Gödel's constructible universe: `CH`, `V=L`, no measurable. -/
def godel : World Claim
  | CH => true | VeqL => true | Meas => false

/-- A Cohen extension refuting `CH`. -/
def cohen : World Claim
  | CH => false | VeqL => false | Meas => false



/-! ## Bridge: modal contingency = multiverse independence

The base multiverse file calls a sentence **independent** in `M` when it is true
in some admissible world and false in another.  Here we show this is *exactly*
modal **contingency** `◇p ∧ ◇¬p` in the **full-accessibility** forcing frame,
where every admissible world is a forcing extension of every other.  This closes
the conceptual gap between the two files with a single general theorem. -/

/-- Modal independence of `p` in a frame: `p` is satisfied at some admissible
    world and refuted at some admissible world. -/
def MIndependent {α} (R : World α → World α → Prop) (M : Multiverse α)
    (p : MSentence α) : Prop :=
  (∃ v ∈ M, meval R M v p) ∧ (∃ v ∈ M, ¬ meval R M v p)

/-- The **full-accessibility forcing frame**: every world is a forcing extension
    of every other, over the full multiverse.  It is trivially reflexive,
    transitive and directed, hence a genuine forcing frame validating `S4.2`. -/
def fullFrame (α : Type*) : ForcingFrame α where
  R := fun _ _ => True
  M := Set.univ
  refl := fun _ _ => trivial
  trans := fun _ _ _ _ _ => trivial
  dir := fun _ _ v₁ _ _ _ _ _ => ⟨v₁, trivial, trivial, trivial⟩




end MultiverseModalForcing


