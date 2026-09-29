-- Prove2me | Definitions.Def_Logic_AbstractAlgebra_ReflectiveOracleHierarchy
-- name    : Logic_AbstractAlgebra_ReflectiveOracleHierarchy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:24:37.803822+00:00
-- url     : https://prove2.me/theorems/157456f2-9659-44c5-b9ab-9fb88625e3d4
-- title:
--   Aether Catalog definitions — Logic_AbstractAlgebra_ReflectiveOracleHierarchy
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.AbstractAlgebra.ReflectiveOracleHierarchy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/AbstractAlgebra/ReflectiveOracleHierarchy.lean by skeleton subtraction
import Mathlib

/-!
# Reflective Oracle Hierarchies: The Consistency-Soundness Asymmetry

This module formalizes the theory of **reflective theories** — formal theories that
simultaneously track provability and truth — and proves a fundamental asymmetry:
while consistency can be resolved by a single oracle jump, soundness cannot.

## Mathematical Context

In proof theory, a central phenomenon is the gap between what a theory can prove
and what is true. Gödel's incompleteness theorems show that sufficiently strong
consistent theories cannot prove their own consistency. Tarski's undefinability
theorem shows they cannot define their own truth predicate. But these two
limitations have different *quantifier complexity*:

- **Consistency** is Σ₁: "there is no proof of ⊥" can be witnessed by checking
  all proofs up to a given length. One oracle jump (adding Con(T)) resolves it.
- **Soundness** is Π₂: "for all φ, if □φ then Tφ" requires checking infinitely
  many sentences. No finite number of oracle jumps resolves full soundness.

This creates a **permanent gap** in the oracle hierarchy that grows with each level.

## Main Definitions

- `ReflectiveTheory` — A theory with provability, truth, and their interaction
- `ReflectiveHierarchy` — The ℕ-indexed tower of reflective theories
- `SoundnessWitness` — Canonical witnesses for incompleteness at each level
- `ProofComplexity` — Proof length functions for speed-up phenomena

## Main Results

- `consistency_one_jump` — Consistency is resolved by a single oracle jump
- `soundness_gap_persistent` — The completeness gap persists across all levels
- `permanent_incompleteness` — No level of the hierarchy is complete
- `consistency_completeness_asymmetry` — The fundamental asymmetry theorem
- `goedel_first_reflective` — Gödel's first incompleteness in reflective setting
- `provable_strict_mono` — The hierarchy is strictly increasing
- `frontier_advancement` — The frontier of ignorance advances but never disappears
- `reflective_hierarchy_exists` — Concrete existence of a reflective hierarchy
-/

noncomputable section

open Set Function

/-! ## Part 1: Reflective Theories -/

/-- A **ReflectiveTheory** models a formal theory with both a provability predicate
    and a truth predicate. Soundness is *not* assumed — this is what we study. -/
structure ReflectiveTheory where
  /-- The type of sentences -/
  Sentence : Type*
  /-- Provability predicate -/
  Provable : Sentence → Prop
  /-- Truth predicate -/
  True_ : Sentence → Prop
  /-- A distinguished bottom (contradiction) sentence -/
  bot : Sentence
  /-- Bottom is not true -/
  bot_not_true : ¬ True_ bot

/-- A reflective theory is **consistent** if it does not prove ⊥. -/
def ReflectiveTheory.Consistent (T : ReflectiveTheory) : Prop :=
  ¬ T.Provable T.bot

/-- A reflective theory is **sound** if everything provable is true. -/
def ReflectiveTheory.Sound (T : ReflectiveTheory) : Prop :=
  ∀ φ, T.Provable φ → T.True_ φ

/-- A reflective theory is **complete** if every true sentence is provable. -/
def ReflectiveTheory.Complete (T : ReflectiveTheory) : Prop :=
  ∀ φ, T.True_ φ → T.Provable φ

/-- The **soundness gap**: sentences provable but not true. -/
def ReflectiveTheory.SoundnessGap (T : ReflectiveTheory) : Set T.Sentence :=
  { φ | T.Provable φ ∧ ¬ T.True_ φ }

/-- The **completeness gap**: sentences true but not provable. -/
def ReflectiveTheory.CompletenessGap (T : ReflectiveTheory) : Set T.Sentence :=
  { φ | T.True_ φ ∧ ¬ T.Provable φ }



/-! ## Part 2: The Reflective Hierarchy -/

/-- A **ReflectiveHierarchy** is a sequence of theories with shared sentences,
    each extending the previous by oracle jumps. The key structural properties:
    monotonicity, strictness, consistency resolution, and permanent incompleteness. -/
structure ReflectiveHierarchy where
  /-- The shared sentence type -/
  Sentence : Type*
  /-- Provability at each level -/
  Provable : ℕ → Sentence → Prop
  /-- Truth predicate (the "intended interpretation") -/
  True_ : Sentence → Prop
  /-- Bottom sentence -/
  bot : Sentence
  /-- Bottom is not true -/
  bot_not_true : ¬ True_ bot
  /-- Monotonicity: higher levels prove more -/
  mono : ∀ n φ, Provable n φ → Provable (n + 1) φ
  /-- Strictness: each level adds something new -/
  strict : ∀ n, ∃ φ, Provable (n + 1) φ ∧ ¬ Provable n φ
  /-- Consistency sentence for each level -/
  conSentence : ℕ → Sentence
  /-- Each consistency sentence is true -/
  con_true : ∀ n, True_ (conSentence n)
  /-- Incompleteness: level n cannot prove its own consistency -/
  con_unprovable : ∀ n, ¬ Provable n (conSentence n)
  /-- Consistency resolution: level n+1 proves consistency of level n -/
  con_jump : ∀ n, Provable (n + 1) (conSentence n)

/-- Extract the reflective theory at a given level. -/
def ReflectiveHierarchy.theoryAt (H : ReflectiveHierarchy) (n : ℕ) :
    ReflectiveTheory where
  Sentence := H.Sentence
  Provable := H.Provable n
  True_ := H.True_
  bot := H.bot
  bot_not_true := H.bot_not_true


/-! ## Part 3: Core Asymmetry Results -/





/-! ## Part 4: Soundness Witnesses and the Asymmetry Theorem -/

/-- A **SoundnessWitness** provides, for each level n, a specific true sentence
    not provable at level n but provable at level n+1. -/
structure SoundnessWitness (H : ReflectiveHierarchy) where
  witness : ℕ → H.Sentence
  witness_true : ∀ n, H.True_ (witness n)
  witness_unprovable : ∀ n, ¬ H.Provable n (witness n)
  witness_resolved : ∀ n, H.Provable (n + 1) (witness n)

/-- Every reflective hierarchy has a canonical soundness witness. -/
def ReflectiveHierarchy.canonicalWitness (H : ReflectiveHierarchy) :
    SoundnessWitness H where
  witness := H.conSentence
  witness_true := H.con_true
  witness_unprovable := H.con_unprovable
  witness_resolved := H.con_jump



/-! ## Part 5: Gödel Sentences in Reflective Theories -/

/-- A **Gödel sentence** is true iff not provable. -/
def ReflectiveTheory.IsGoedelSentence (T : ReflectiveTheory) (φ : T.Sentence) : Prop :=
  T.True_ φ ↔ ¬ T.Provable φ




/-! ## Part 6: Strict Monotonicity -/



/-! ## Part 7: Speed-up Phenomenon -/

/-- A **proof complexity** function assigns proof length to each provable sentence. -/
structure ProofComplexity (H : ReflectiveHierarchy) where
  length : ℕ → H.Sentence → ℕ
  pos_of_provable : ∀ n φ, H.Provable n φ → 0 < length n φ
  zero_of_unprovable : ∀ n φ, ¬ H.Provable n φ → length n φ = 0


/-! ## Part 8: Union Theory (ω-limit) -/

/-- The **union theory**: provable iff provable at some finite level. -/
def ReflectiveHierarchy.unionProvable (H : ReflectiveHierarchy) (φ : H.Sentence) : Prop :=
  ∃ n, H.Provable n φ




/-! ## Part 9: The Gap Transfer and Frontier Advancement -/




/-! ## Part 10: Concrete Construction -/

/-- Construct a concrete reflective hierarchy from an injective witness function.
    Sentences are ℕ, provability at level n means "is a witness for some k < n". -/
def mkReflectiveHierarchy
    (witness : ℕ → ℕ)
    (h_inj : Function.Injective witness)
    (bot_val : ℕ)
    (h_bot : ∀ k, bot_val ≠ witness k) :
    ReflectiveHierarchy where
  Sentence := ℕ
  Provable := fun n s => ∃ k, k < n ∧ s = witness k
  True_ := fun s => ∃ k, s = witness k
  bot := bot_val
  bot_not_true := fun ⟨k, hk⟩ => h_bot k hk
  mono := fun n s ⟨k, hk, hs⟩ => ⟨k, by omega, hs⟩
  strict := fun n => ⟨witness n, ⟨n, by omega, rfl⟩, fun ⟨k, hk, hs⟩ => by
    have := h_inj hs; omega⟩
  conSentence := witness
  con_true := fun n => ⟨n, rfl⟩
  con_unprovable := fun n ⟨k, hk, hs⟩ => by have := h_inj hs; omega
  con_jump := fun n => ⟨n, by omega, rfl⟩

/-- **Existence theorem**: Reflective hierarchies with all structural properties exist. -/
private def oddWitness : ℕ → ℕ := fun k => 2 * k + 1




/-! ## Conjecture -/


end


