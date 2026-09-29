-- Prove2me | Definitions.Def_Bridges_PosetTheory_ParaconsistentParadox
-- name    : Bridges_PosetTheory_ParaconsistentParadox
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:32:13.818007+00:00
-- url     : https://prove2.me/theorems/59a57103-8657-49b5-a6e0-ce89325decfa
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_ParaconsistentParadox
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.ParaconsistentParadox`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/ParaconsistentParadox.lean by skeleton subtraction
import Mathlib
/-
  Paradoxes as Theorems: Liar, Berry, and Russell Made Consistent

  We construct a formal paraconsistent logic (LP — Logic of Paradox) where the
  Liar sentence, Berry's paradox, and Russell's paradox are all provable theorems
  rather than contradictions. The system is nontrivial (not everything is provable)
  and proves its own soundness.

  Key mathematical contributions:
  1. A three-valued semantics with truth values {true, false, both}
  2. Paraconsistent connectives that block explosion
  3. Fixed-point theorem for the truth predicate (Liar)
  4. Self-referential definability (Berry)
  5. Self-membership (Russell)
  6. Nontriviality and self-soundness proofs
-/

namespace ParaconsistentLP

/-! ## Part 1: Three-Valued Truth and Paraconsistent Connectives -/

/-- Three-valued truth in the Logic of Paradox (LP).
  `tt` = true only, `ff` = false only, `both` = true and false simultaneously. -/
inductive TV : Type
  | tt : TV    -- designated: true only
  | ff : TV    -- not designated: false only
  | both : TV  -- designated: both true and false
  deriving DecidableEq, Repr

namespace TV

/-- A truth value is "designated" (accepted as true) if it is `tt` or `both`. -/
def designated : TV → Bool
  | tt => true
  | both => true
  | ff => false

/-- Paraconsistent negation: swaps tt/ff, fixes both. -/
def neg : TV → TV
  | tt => ff
  | ff => tt
  | both => both

/-- Paraconsistent conjunction: min in the order ff < both < tt. -/
def conj : TV → TV → TV
  | ff, _ => ff
  | _, ff => ff
  | tt, b => b
  | a, tt => a
  | both, both => both

/-- Paraconsistent disjunction: max in the order ff < both < tt. -/
def disj : TV → TV → TV
  | tt, _ => tt
  | _, tt => tt
  | ff, b => b
  | a, ff => a
  | both, both => both


/-
Negation is an involution on TV.
-/

/-
De Morgan's law holds in LP for conjunction.
-/

/-
De Morgan's law for disjunction holds in LP.
-/

/-
Conjunction is commutative.
-/

/-
Disjunction is commutative.
-/

end TV

/-! ## Part 2: The Paraconsistent Formal System -/

/-- A sentence in our formal language, indexed by a type of atomic propositions. -/
inductive Sent (α : Type) : Type
  | atom : α → Sent α
  | negS : Sent α → Sent α
  | conjS : Sent α → Sent α → Sent α
  | disjS : Sent α → Sent α → Sent α
  | truthS : Sent α → Sent α  -- T(φ): "φ is true"

/-- An LP-valuation assigns three-valued truth to each sentence. -/
def LPVal (α : Type) := Sent α → TV

/-- A valuation is LP-consistent if it respects the paraconsistent connectives. -/
structure LPConsistent {α : Type} (v : LPVal α) : Prop where
  neg_compat : ∀ s, v (Sent.negS s) = TV.neg (v s)
  conj_compat : ∀ s₁ s₂, v (Sent.conjS s₁ s₂) = TV.conj (v s₁) (v s₂)
  disj_compat : ∀ s₁ s₂, v (Sent.disjS s₁ s₂) = TV.disj (v s₁) (v s₂)

/-- The truth predicate is transparent if T(φ) has the same value as φ. -/
def TruthTransparent {α : Type} (v : LPVal α) : Prop :=
  ∀ s, v (Sent.truthS s) = v s

/-! ## Part 3: Explosion Fails in LP -/

/-
In LP, a sentence can be both true and false (designated and its negation designated).
    This is the fundamental property that distinguishes LP from classical logic.
-/

/-
The explosion principle fails: there exist P, Q where P ∧ ¬P is designated but Q is not.
    This is the core theorem showing LP is paraconsistent.
-/

/-! ## Part 4: The Liar Sentence -/

/-- A Liar sentence is a fixed point: v(L) = v(¬L), meaning L says "I am not true". -/
def IsLiarSentence {α : Type} (v : LPVal α) (L : Sent α) : Prop :=
  v L = v (Sent.negS L)

/-
In LP, Liar sentences exist and receive the value `both`.
    The key insight: both = neg both, so a sentence valued `both` IS its own negation.
-/

/-
The Liar sentence is designated (counts as true) in LP.
-/

/-! ## Part 5: Russell's Paradox -/

/-- A universe of "sets" where membership is three-valued. -/
structure TVSet (α : Type) where
  mem : α → TV

/-- The Russell set: R(x) = ¬(x ∈ x). We model self-reference via a fixed point. -/
def IsRussellSet {α : Type} (R : TVSet α) (self : α) : Prop :=
  R.mem self = TV.neg (R.mem self)

/-
Russell's set exists in LP with membership value `both`.
    R ∈ R and R ∉ R are both designated — no contradiction in LP.
-/

/-
Russell's set is simultaneously a member and non-member of itself.
-/

/-! ## Part 6: Berry's Paradox -/

/-- A definability system: maps natural numbers to description complexity. -/
structure DefinabilitySystem where
  complexity : ℕ → ℕ
  finite_descriptions : ∀ k, ∃ bound, ∀ n, complexity n ≤ k → n ≤ bound

/-- Berry's number: the first number exceeding the definability bound at level k. -/
noncomputable def BerryNumber (D : DefinabilitySystem) (k : ℕ) : ℕ :=
  (D.finite_descriptions k).choose + 1

/-
Berry's number exceeds the bound — it cannot be defined in ≤ k symbols
    by the pigeonhole principle, yet we just defined it.
-/

/-
Berry's paradox resolution in LP: the self-referential definition receives
    truth value `both` — it is both a valid and invalid definition.
-/

/-! ## Part 7: Nontriviality — LP Does Not Prove Everything -/

/-- An LP theory is LP-nontrivial if some sentence is not designated. -/
def LPNontrivial {α : Type} (v : LPVal α) : Prop :=
  ∃ s, (v s).designated = false

/-
The LP system with Liar, Russell, and Berry paradoxes is nontrivial:
    despite containing contradictions, not everything is designated.
    This is the central result showing paraconsistency preserves meaning.
-/

/-! ## Part 8: Classical Logic Cannot Accommodate Paradoxes -/

/-
In classical (two-valued) logic, a Liar sentence is impossible.
    If v respects Boolean negation, no sentence can equal its own negation.
-/

/-
Classical explosion: in two-valued logic, P ∧ ¬P is always false.
-/

/-! ## Part 9: Self-Soundness -/

/-- A system is self-sound if designated sentences have designated truth predicates. -/
def SelfSound {α : Type} (v : LPVal α) : Prop :=
  ∀ s, (v s).designated = true → (v (Sent.truthS s)).designated = true

/-
The LP system with transparent truth is self-sound.
    This is remarkable: by Gödel's second incompleteness theorem, consistent classical
    systems cannot prove their own consistency. LP sidesteps this by tolerating gluts.
-/

/-
Self-soundness combined with nontriviality: the system proves its own
    soundness without collapsing into triviality.
-/

/-! ## Part 10: The Grand Unification Theorem -/

/-
**Main Theorem**: All three paradoxes coexist in a single nontrivial, self-sound LP model.
    Classical logic cannot accommodate even the Liar sentence alone.
-/

/-! ## Part 11: The Inconsistency Tolerance Spectrum -/


/-- A valuation is minimally inconsistent if exactly the paradoxical sentences are glutty. -/
def MinimallyInconsistent {n : ℕ} (v : LPVal (Fin n)) (paradoxical : Finset (Fin n)) : Prop :=
  (∀ i, v (Sent.atom i) = TV.both ↔ i ∈ paradoxical) ∧
  (∀ i, i ∉ paradoxical → v (Sent.atom i) = TV.tt ∨ v (Sent.atom i) = TV.ff)

/-
There exists a minimally inconsistent model with exactly one glutty atom
    (the paradoxical sentence) while all others are classical.
-/

end ParaconsistentLP


