-- Prove2me | Theorems.Thm_Bridges_AlgebraEMLComputation_IdempotentThermodynamicRealization_ThermoAut_quotientAut_minimal
-- name    : Bridges.AlgebraEMLComputation.IdempotentThermodynamicRealization.ThermoAut.quotientAut_minimal
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:19:29.023753+00:00
-- url     : https://prove2.me/theorems/85247f95-95f1-4f70-8265-10bdc5694170
-- title:
--   QuotientAut minimal
-- statement:
--   Formal statement of `Bridges.AlgebraEMLComputation.IdempotentThermodynamicRealization.ThermoAut.quotientAut_minimal` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Bridges.AlgebraEMLComputation.IdempotentThermodynamicRealization.ThermoAut.quotientAut_minimal{Q' : Type*}
--       [Fintype Q] [Fintype Q']
--       (A : ThermoAut S σ Q) (B : ThermoAut S σ Q')
--       (hbeh : A.behavior = B.behavior)
--       (hA_surj : ∀ q : Q, ∃ w, A.run A.init w = q) :
--       Fintype.card (ThermoState A) ≤ Fintype.card Q' := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/IdempotentThermodynamicRealization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/IdempotentThermodynamicRealization.lean#L220

-- Thm stub generated from Bridges/IdempotentThermodynamicRealization.lean
import Mathlib
import Definitions.Def_Bridges_IdempotentThermodynamicRealization
/-
# Idempotent Thermodynamic Realization via Closure Entropy and Free-Energy Minimization

This file formalizes a **thermodynamic Myhill–Nerode theorem**: a canonical minimization
principle for deterministic automata with observable outputs, where "observation" is
mediated by a closure operator and an entropy functional, and the free-energy observable
determines the finest useful state equivalence.

## Main Results

- `wordEquiv_right_congruence` — Free-energy indistinguishability is a right congruence.
- `thermoState_finite` — The quotient by behavioral equivalence has finitely many states.
- `quotientAut_behavior_eq` — The quotient automaton realizes the same behavior.
- `quotientAut_minimal` — The quotient is minimal among all behaviorally equivalent automata.
- `gibbsHankelRank_eq_card_thermoState` — The Gibbs–Hankel generator rank equals the
  number of quotient states.
- `freeEnergy_min_commutes_closure` — Free-energy minimization commutes with closure
  saturation.
- `optimal_paths_same_dissipation` — Optimal paths share a conserved dissipation class.

## Bridges

- **Automata Theory ↔ Tropical Algebra**: Myhill–Nerode via idempotent free energy
- **Statistical Mechanics ↔ Computation**: Free energy as canonical observable
- **Closure Semantics ↔ Minimization**: Coarse-graining commutes with optimization
- **EML ↔ Tropical Geometry**: Generator rank = tropical dimension of computation
-/


open Function List Classical

noncomputable section

open Bridges.AlgebraEMLComputation.IdempotentThermodynamicRealization

/-! ## §1. Thermodynamic Automaton: Core Structure -/


variable {S σ Q : Type*}

/-! ## §2. Running the Automaton on Words -/





/-! ## §3. Behavior and Residuals -/





/-! ## §4. State Behavioral Equivalence (Thermodynamic Equivalence) -/







/-! ## §5. Word-Level Indistinguishability -/




/-! ## §6. Right Congruence -/



/-! ## §7. Quotient State Space (Thermodynamic States) -/




/-! ## §8. Quotient Automaton Construction -/





/-! ## §9. Behavior Preservation -/


/-! ## §10. Minimality of the Quotient Automaton -/

/-
**Minimality theorem**: if automaton `B` with state space `Q'` has the same
    global behavior as `A`, then `A`'s quotient has at most `|Q'|` states.

    Key insight: if two words reach the same B-state, they produce the same output
    on all continuations (since behaviors agree), hence are in the same A-equivalence class.
    So distinct A-classes map to distinct B-states.
-/

theorem Bridges.AlgebraEMLComputation.IdempotentThermodynamicRealization.ThermoAut.quotientAut_minimal{Q' : Type*}
    [Fintype Q] [Fintype Q']
    (A : ThermoAut S σ Q) (B : ThermoAut S σ Q')
    (hbeh : A.behavior = B.behavior)
    (hA_surj : ∀ q : Q, ∃ w, A.run A.init w = q) :
    Fintype.card (ThermoState A) ≤ Fintype.card Q' := by sorry
