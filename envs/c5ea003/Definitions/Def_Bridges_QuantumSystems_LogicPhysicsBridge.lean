-- Prove2me | Definitions.Def_Bridges_QuantumSystems_LogicPhysicsBridge
-- name    : Bridges_QuantumSystems_LogicPhysicsBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:37:07.542742+00:00
-- url     : https://prove2.me/theorems/a73151f1-3b6a-4831-b905-da9c4c015a72
-- title:
--   Aether Catalog definitions — Bridges_QuantumSystems_LogicPhysicsBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.QuantumSystems.LogicPhysicsBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/QuantumSystems/LogicPhysicsBridge.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Formal Foundations for the Logic–Physics Bridge

This file develops an abstract framework relating **physical realizability** of a theory
(having a model — a "world" that satisfies it) to its **proof-theoretic consistency**
(non-provability of falsum). The central theme is the asymmetry between the two notions:

* *Physical consistency implies mathematical consistency* — if a theory has a model and the
  proof system is honest about contradictions, then it cannot prove falsum.
* *Mathematical consistency does not imply physical consistency* — a syntactically consistent
  theory can fail to have any model (the **separation theorem**, witnessed by an empty world).

We also isolate the exact strength needed for the physics → logic bridge: not full soundness,
but only **falsum-soundness** (honesty about contradictions); we show this generalization is
proper. Finally we sketch two extensions:

* a **completeness collapse** (Direction 1): for *complete* sound semantics the two notions of
  consistency coincide — a formal "phase boundary" between logic and physics;
* a **quantum strengthening** (Direction 4): a superposition-closed notion of physical
  consistency that is strictly stronger than ordinary physical consistency.

## Main results

* `consistency_antimono` — consistency is anti-monotone under theory extension.
* `proper_extension_new_theorem` — an unprovable sentence yields a proper, new-theorem extension.
* `model_implies_consistency_weak` — falsum-soundness + a model ⟹ consistency.
* `sound_implies_falsum_sound` — full soundness ⟹ falsum-soundness.
* `model_implies_consistency` / `physical_implies_mathematical` — the physics → logic bridge.
* `falsum_sound_strictly_weaker` — falsum-soundness ⊊ full soundness (proper generalization).
* `math_consistency_not_sufficient` — separation: consistency ↛ having a model.
* `completeness_collapse` — for complete sound semantics, consistency ↔ physical consistency.
* `quantum_implies_physical` / `quantum_strictly_stronger` — the quantum hierarchy.
-/

namespace LogicPhysics

universe u
variable {S : Type u}

/-! ## §1. Abstract proof systems and syntactic consistency -/

/-- An abstract proof system over a type `S` of sentences: a distinguished falsum `bot`,
a consequence relation `Proves`, closed under weakening (`mono`) and containing assumptions. -/
structure ProofSystem (S : Type u) where
  /-- The falsum / absurdity sentence. -/
  bot : S
  /-- `Proves Γ φ` means `φ` is derivable from the set of hypotheses `Γ`. -/
  Proves : Set S → S → Prop
  /-- Weakening: enlarging the hypotheses preserves derivability. -/
  mono : ∀ {Γ Δ : Set S} {φ : S}, Γ ⊆ Δ → Proves Γ φ → Proves Δ φ
  /-- Reflexivity / assumption rule: a hypothesis is derivable from itself. -/
  assumption : ∀ {Γ : Set S} {φ : S}, φ ∈ Γ → Proves Γ φ

/-- A theory `T` is (syntactically / mathematically) **consistent** for `P` when it does not
prove falsum. -/
def Consistent (P : ProofSystem S) (T : Set S) : Prop := ¬ P.Proves T P.bot

-- !-- Consistency is anti-monotone: if a larger theory is consistent so is any subtheory,
-- since a falsum proof of the subtheory would lift by weakening (`P.mono`). -- !--

-- !-- An unprovable sentence `φ` is genuinely outside `T` (else the assumption rule would
-- derive it) yet is a theorem of `insert φ T`, so the extension is proper and gains a theorem. -- !--

/-! ## §2. Semantics, models, and soundness -/

/-- A semantics ("physics") for a proof system `P`: a type of `World`s, a satisfaction
relation `sat`, and the requirement that no world realizes falsum. -/
structure Semantics (P : ProofSystem S) where
  /-- The type of worlds / physical realizations. -/
  World : Type
  /-- `sat w φ` means world `w` satisfies sentence `φ`. -/
  sat : World → S → Prop
  /-- No world satisfies falsum. -/
  bot_unsat : ∀ w, ¬ sat w P.bot

/-- `T` **has a model** in the semantics `M` when some world satisfies every sentence of `T`. -/
def HasModel {P : ProofSystem S} (M : Semantics P) (T : Set S) : Prop :=
  ∃ w : M.World, ∀ φ ∈ T, M.sat w φ

/-- **Physical consistency**: a theory is physically consistent (in the given physics `M`) when
it is realizable, i.e. it has a model. -/
def PhysicallyConsistent {P : ProofSystem S} (M : Semantics P) (T : Set S) : Prop :=
  HasModel M T

/-- Full **soundness**: every derivable sentence is true in every world satisfying the
hypotheses. -/
def Sound {P : ProofSystem S} (M : Semantics P) : Prop :=
  ∀ {Γ : Set S} {φ : S} (w : M.World), P.Proves Γ φ → (∀ ψ ∈ Γ, M.sat w ψ) → M.sat w φ

/-- **Falsum-soundness**: the proof system is merely "honest about contradictions" — whenever
falsum is derivable from hypotheses satisfied by `w`, then `w` satisfies falsum (which, with
`bot_unsat`, is impossible). This is the precise strength the bridge needs. -/
def FalsumSound {P : ProofSystem S} (M : Semantics P) : Prop :=
  ∀ {Γ : Set S} (w : M.World), P.Proves Γ P.bot → (∀ ψ ∈ Γ, M.sat w ψ) → M.sat w P.bot

-- !-- The bridge, weak form: from a model `w` of `T`, a falsum proof would force `w` to satisfy
-- falsum via falsum-soundness, contradicting `bot_unsat`. Only honesty about ⊥ is used. -- !--

-- !-- Full soundness specializes to falsum-soundness by taking `φ = bot`. -- !--

-- !-- The physics → logic bridge: soundness gives falsum-soundness, then a model gives
-- consistency. -- !--

-- !-- Restated: physical consistency (realizability) implies mathematical consistency. -- !--

/-! ## §3. The generalization is proper: falsum-soundness ⊊ soundness -/

-- !-- Over `S = ℕ` with the rule `p ⊢ q` (encoded `1 ∈ Γ → q = 2`) and the single world where
-- only `p` (=1) holds: falsum-soundness holds (a ⊥-proof must use ⊥ as a hypothesis, which the
-- model would already satisfy), but soundness fails on the rule `{1} ⊢ 2` since `2` is unsatisfied. -- !--

/-! ## §4. Separation: mathematical consistency does not imply physical consistency -/

-- !-- Take the pure-assumption proof system over `ℕ` (which proves only its hypotheses) and the
-- physics whose world type is `Empty`. The empty theory is consistent (`0 ∉ ∅`) and the
-- semantics is vacuously sound, yet no world exists, so `∅` has no model. -- !--

/-! ## §5. Completeness collapse (Direction 1): the logic–physics phase boundary -/

/-- A semantics is **complete** for `P` when every consistent theory has a model — the converse
of the soundness bridge. -/
def Complete {P : ProofSystem S} (M : Semantics P) : Prop :=
  ∀ T : Set S, Consistent P T → HasModel M T

-- !-- For sound *and* complete semantics the two consistency notions coincide: completeness gives
-- the syntactic → semantic direction, the soundness bridge gives the reverse. -- !--

/-! ## §6. Quantum strengthening (Direction 4): superposition-closed realizability -/

/-- A semantics equipped with a `superpose` operation on worlds (a structured space of physical
realizations). -/
structure QSemantics (P : ProofSystem S) extends Semantics P where
  /-- Combine two worlds into a "superposition" world. -/
  superpose : World → World → World

/-- **Quantum physical consistency**: `T` has a model, and the set of models is closed under
superposition (combining two realizations yields a realization). -/
def QuantumPhysicallyConsistent {P : ProofSystem S} (Q : QSemantics P) (T : Set S) : Prop :=
  (∃ w, ∀ φ ∈ T, Q.sat w φ) ∧
  (∀ w1 w2, (∀ φ ∈ T, Q.sat w1 φ) → (∀ φ ∈ T, Q.sat w2 φ) →
    (∀ φ ∈ T, Q.sat (Q.superpose w1 w2) φ))

-- !-- Quantum physical consistency includes ordinary physical consistency as its first
-- component. -- !--

-- !-- The strengthening is proper: with worlds `Bool`, `sat w φ := (φ = 1 ∧ w = true)` and
-- `superpose := fun _ _ => false`, the theory `{1}` has the model `true` but superposing the two
-- (identical) models lands in `false`, which is not a model — so closure fails. -- !--

end LogicPhysics


