-- Prove2me | Definitions.Def_Logic_Multiverse_BooleanValuedRealization
-- name    : Logic_Multiverse_BooleanValuedRealization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:57:54.763103+00:00
-- url     : https://prove2.me/theorems/dae2d215-d41b-49f2-87d7-9ec03c78e3f9
-- title:
--   Aether Catalog definitions — Logic_Multiverse_BooleanValuedRealization
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.Multiverse.BooleanValuedRealization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/Multiverse/BooleanValuedRealization.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_Multiverse_ButtonsSwitches
/-
# Internal Boolean-Valued Realization of the Forcing Multiverse

This file answers *Direction 1* of the multiverse research programme: it builds a
**Boolean-valued universe whose generic quotients instantiate the abstract forcing
frame**, with forcing closure, directedness and the two opposite Continuum
Hypothesis branches **derived** from the construction rather than assumed as frame
axioms.

The development has four layers.

## Layer A — Boolean-valued semantics and generic quotients

Over an arbitrary Boolean algebra `B` we give the Boolean value `bval v p ∈ B` of a
propositional set-theoretic assertion `p`, define a **generic filter** (a proper
filter deciding every element), and prove the **truth lemma**

* `sat_quot_iff` : `sat (quot v U) p ↔ U.mem (bval v p)` ,

the propositional core of the Boolean-valued-model quotient theorem: the two-valued
quotient satisfies exactly the assertions whose Boolean value lies in the generic
filter.  Around it:

* `bval_eq_top_of_provable` — **forcing closure**: every theorem of classical
  propositional logic has Boolean value `⊤` (soundness of Boolean-valued semantics
  for a Hilbert calculus, by induction on derivations);
* `sat_quot_of_provable`, `sat_quot_of_forces` — everything forced by a condition
  in the generic filter is true in the quotient;
* `branch_of_undecided` — **branching**: an assertion whose Boolean value is
  neither `⊥` nor `⊤` is *true in one generic quotient and false in another*.

## Layer B — the pre-Boolean control frame of buttons and switches

Worlds are pairs `(S, g)` with `S` a finite set of *pushed buttons* and `g` a
setting of the *switches*; accessibility is `S ⊆ T`.  The frame is reflexive,
transitive and **directed** (`cacc_directed`), hence sound for `S4.2`
(`cacc_T`, `cacc_four`, `cacc_dot2`); pushed buttons are buttons in the sense of
`Catalog/Logic/Multiverse/ButtonsSwitches.lean` (`pushed_is_button`) and switches
are switches (`switch_is_switch`).

## Layer C — the realization: Layer B *is* the generic-quotient frame of Layer A

The Boolean algebra is the powerset `Set (Sw → Bool)` of switch settings; stage `S`
carries the assignment `cassign S`, and the generic filters used are the principal
ones at a generic point `g`.  The main theorem

* `realization` : `csat (S, g) p ↔ g ∈ bval (cassign S) p`

says that the control world `(S, g)` is *exactly* the generic quotient of the
Boolean-valued universe at stage `S` by the generic object `g`.  Consequently:

* `button_of_pos` — every **positive button formula** defines a button, *derived*
  from Boolean-valued monotonicity `bval_mono_of_pos`, not assumed;
* `cassign_union_btn` — amalgamation of stages on the algebra side, matching frame
  directedness;
* `CH_branches_derived` — both CH branches come from `branch_of_undecided` applied
  to the CH switch, whose Boolean value is provably neither `⊥` nor `⊤`;
* `five_fails`, `brouwer_fails` — the realized frame validates `.2` yet refutes
  `5` and `B`, so it is genuinely an `S4.2` frame.

## Layer D — ground/extension bimodality

Adding the converse **ground** modality we prove the mixed tense validity
`p → □ ◇̌ p` (`tense_axiom_valid`) while the unimodal Brouwer analogue `p → □ ◇ p`
**fails** on the very same frame (`brouwer_fails`): a concrete separation of the
mixed logic from the extension-only logic (`bimodal_separation`).  Grounds are
downward directed and possess a least element, the **mantle** (`mantle_least`).
-/

namespace BooleanValuedRealization

open Multiverse

/-! ## Layer A.1 — syntax and Boolean values -/

/-- Propositional set-theoretic assertions over atoms `α`, in the functionally
complete signature `{⊥, →}`. -/
inductive BForm (α : Type*) where
  | atom : α → BForm α
  | fls : BForm α
  | imp : BForm α → BForm α → BForm α
  deriving DecidableEq

namespace BForm
variable {α : Type*}

/-- Negation. -/
def neg (p : BForm α) : BForm α := .imp p .fls
/-- Verum. -/
def tru : BForm α := neg .fls
/-- Disjunction. -/
def disj (p q : BForm α) : BForm α := .imp (neg p) q
/-- Conjunction. -/
def conj (p q : BForm α) : BForm α := neg (.imp p (neg q))

end BForm

variable {α : Type*} {B : Type*} [BooleanAlgebra B]

/-- The **Boolean value** of an assertion in the Boolean-valued universe
determined by the atomic assignment `v`. -/
def bval (v : α → B) : BForm α → B
  | .atom a => v a
  | .fls => ⊥
  | .imp p q => bval v p ⇨ bval v q






/-! ## Layer A.2 — forcing closure: soundness of Boolean-valued semantics -/

section HilbertValues

variable (a b c : B)




end HilbertValues

/-- A Hilbert calculus for classical propositional logic. -/
inductive Provable {α : Type*} : BForm α → Prop
  | ax1 (p q : BForm α) : Provable (.imp p (.imp q p))
  | ax2 (p q r : BForm α) :
      Provable (.imp (.imp p (.imp q r)) (.imp (.imp p q) (.imp p r)))
  | ax3 (p : BForm α) : Provable (.imp (BForm.neg (BForm.neg p)) p)
  | mp {p q : BForm α} : Provable (.imp p q) → Provable p → Provable q


/-! ## Layer A.3 — generic filters and the truth lemma -/

/-- A **generic filter** on a Boolean algebra: a proper filter deciding every
element.  Generic filters are the generic objects whose quotients are the
two-valued universes of the multiverse. -/
structure Generic (B : Type*) [BooleanAlgebra B] where
  /-- Membership in the filter. -/
  mem : B → Prop
  /-- The filter is nontrivial. -/
  top_mem : mem ⊤
  /-- The filter is proper. -/
  bot_notMem : ¬ mem ⊥
  /-- The filter is upward closed. -/
  up : ∀ {a b : B}, mem a → a ≤ b → mem b
  /-- The filter is closed under meets. -/
  inf_mem : ∀ {a b : B}, mem a → mem b → mem (a ⊓ b)
  /-- Genericity: every element is decided. -/
  decides : ∀ a : B, mem a ∨ mem aᶜ

namespace Generic
variable (U : Generic B)



end Generic

/-- Two-valued satisfaction of an assertion at a two-valued world. -/
def sat (w : α → Prop) : BForm α → Prop
  | .atom a => w a
  | .fls => False
  | .imp p q => sat w p → sat w q





/-- The **generic quotient**: the two-valued world obtained from the Boolean-valued
universe by collapsing along the generic filter `U`. -/
def quot (v : α → B) (U : Generic B) : α → Prop := fun a => U.mem (v a)



/-- A **condition** `b` forces `p` when `b ≤ ⟦p⟧`. -/
def Forces (v : α → B) (b : B) (p : BForm α) : Prop := b ≤ bval v p




/-! ## Layer A.4 — branching -/

/-- A Boolean algebra is **rich** when every nonzero element lies in some generic
filter (the Boolean prime ideal principle for `B`). -/
def Rich (B : Type*) [BooleanAlgebra B] : Prop :=
  ∀ b : B, b ≠ ⊥ → ∃ U : Generic B, U.mem b


/-- The principal generic filter at a point of a powerset algebra. -/
def principalGeneric {Ω : Type*} (x : Ω) : Generic (Set Ω) where
  mem := fun s => x ∈ s
  top_mem := trivial
  bot_notMem := id
  up := fun h hle => hle h
  inf_mem := fun h1 h2 => ⟨h1, h2⟩
  decides := fun s => by
    by_cases hx : x ∈ s
    · exact Or.inl hx
    · exact Or.inr hx



/-! ## Layer B — the pre-Boolean control frame of buttons and switches -/

section Control

variable {Btn Sw : Type*}

/-- A **control world**: a finite set of pushed buttons together with a setting of
all switches. -/
abbrev CWorld (Btn Sw : Type*) := Finset Btn × (Sw → Bool)

/-- **Forcing accessibility**: an extension may push further buttons and reset the
switches arbitrarily, but can never unpush a button. -/
def cacc (w v : CWorld Btn Sw) : Prop := w.1 ⊆ v.1




/-! ### `S4.2` soundness of the control frame -/





/-! ### Buttons and switches -/

/-- The assertion "button `b` has been pushed". -/
def pushedP (b : Btn) : CWorld Btn Sw → Prop := fun w => b ∈ w.1

/-- The assertion "switch `s` is on". -/
def switchP (s : Sw) : CWorld Btn Sw → Prop := fun w => w.2 s = true




/-! ### Failure of `5`: the frame is `S4.2`, not `S5` -/



end Control

/-! ## Layer C — the Boolean-valued realization of the control frame -/

section Realization

variable {Btn Sw : Type*}

/-- Atomic set-theoretic assertions: button assertions (persistent) and switch
assertions (toggleable, e.g. the Continuum Hypothesis). -/
inductive CAtom (Btn Sw : Type*) where
  | btn : Btn → CAtom Btn Sw
  | sw : Sw → CAtom Btn Sw
  deriving DecidableEq

/-- The space of generic objects: all switch settings. -/
abbrev Gen (Sw : Type*) := Sw → Bool

/-- The Boolean-valued assignment at **stage** `S` (the set of buttons already
pushed): a pushed button gets value `⊤`, an unpushed one `⊥`, and a switch gets the
set of generic objects turning it on. -/
def cassign (S : Finset Btn) : CAtom Btn Sw → Set (Gen Sw)
  | .btn b => {_g | b ∈ S}
  | .sw s => {g | g s = true}

/-- The atomic diagram of a control world. -/
def atomTrue (w : CWorld Btn Sw) : CAtom Btn Sw → Prop
  | .btn b => b ∈ w.1
  | .sw s => w.2 s = true

/-- Two-valued satisfaction at a control world. -/
def csat (w : CWorld Btn Sw) (p : BForm (CAtom Btn Sw)) : Prop := sat (atomTrue w) p




/-! ### Positive button formulas and derived forcing closure -/

/-- The **positive button fragment**: built from button atoms by conjunction and
disjunction (and verum).  These are the assertions that forcing can only make
*more* true as buttons get pushed. -/
inductive Pos : BForm (CAtom Btn Sw) → Prop
  | atom (b : Btn) : Pos (.atom (.btn b))
  | tru : Pos BForm.tru
  | conj {p q} : Pos p → Pos q → Pos (p.conj q)
  | disj {p q} : Pos p → Pos q → Pos (p.disj q)





/-! ### The Continuum Hypothesis branches, derived -/

/-- The CH atom: a designated switch. -/
def chAtom (s : Sw) : BForm (CAtom Btn Sw) := .atom (.sw s)






end Realization

/-! ## Layer D — ground/extension bimodality -/

section Bimodal

variable {Btn Sw : Type*}

/-- The **ground** relation: `v` is a ground of `w` when it has pushed no more
buttons.  It is the converse of forcing accessibility. -/
def cgnd (w v : CWorld Btn Sw) : Prop := v.1 ⊆ w.1








end Bimodal

end BooleanValuedRealization


