-- Prove2me | Theorems.Thm_LogicPhysics_quantum_strictly_stronger
-- name    : LogicPhysics.quantum_strictly_stronger
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:50:36.595807+00:00
-- url     : https://prove2.me/theorems/f98d9623-b80f-432d-93f6-74681af44c41
-- title:
--   Quantum strictly stronger
-- statement:
--   Formal statement of `LogicPhysics.quantum_strictly_stronger` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem LogicPhysics.quantum_strictly_stronger:
--       ∃ (P : ProofSystem ℕ) (Q : QSemantics P) (T : Set ℕ),
--         PhysicallyConsistent Q.toSemantics T ∧ ¬ QuantumPhysicallyConsistent Q T := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/QuantumSystems/LogicPhysicsBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/QuantumSystems/LogicPhysicsBridge.lean#L220

-- Thm stub generated from Bridges/QuantumSystems/LogicPhysicsBridge.lean
import Mathlib
import Definitions.Def_Bridges_QuantumSystems_LogicPhysicsBridge
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

open LogicPhysics

universe u
variable {S : Type u}

/-! ## §1. Abstract proof systems and syntactic consistency -/



-- !-- Consistency is anti-monotone: if a larger theory is consistent so is any subtheory,
-- since a falsum proof of the subtheory would lift by weakening (`P.mono`). -- !--

-- !-- An unprovable sentence `φ` is genuinely outside `T` (else the assumption rule would
-- derive it) yet is a theorem of `insert φ T`, so the extension is proper and gains a theorem. -- !--

/-! ## §2. Semantics, models, and soundness -/






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


-- !-- For sound *and* complete semantics the two consistency notions coincide: completeness gives
-- the syntactic → semantic direction, the soundness bridge gives the reverse. -- !--

/-! ## §6. Quantum strengthening (Direction 4): superposition-closed realizability -/



-- !-- Quantum physical consistency includes ordinary physical consistency as its first
-- component. -- !--

-- !-- The strengthening is proper: with worlds `Bool`, `sat w φ := (φ = 1 ∧ w = true)` and
-- `superpose := fun _ _ => false`, the theory `{1}` has the model `true` but superposing the two
-- (identical) models lands in `false`, which is not a model — so closure fails. -- !--

theorem LogicPhysics.quantum_strictly_stronger:
    ∃ (P : ProofSystem ℕ) (Q : QSemantics P) (T : Set ℕ),
      PhysicallyConsistent Q.toSemantics T ∧ ¬ QuantumPhysicallyConsistent Q T := by sorry
