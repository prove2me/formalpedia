-- Prove2me | solution 1 for Bridges.AlgebraEMLComputation.IdempotentThermodynamicRealization.ThermoAut.gibbsHankelRank_eq_card_thermoState
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:59:43.702202+00:00
-- url     : https://prove2.me/submissions/f20eff75-5e97-4306-bf99-2c2256f7f729

-- Sol generated from Bridges/IdempotentThermodynamicRealization.lean
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

/-! ## §11. Free-Energy Specific Definitions -/

variable {Obs : Type*}





/-! ## §12. Gibbs–Hankel Semimodule and Generator Rank -/





/-
**Rank–state equality**: the Gibbs–Hankel generator rank equals the number
    of thermodynamic states.
-/

/-! ## §13. Uniqueness Up to Isomorphism -/



/-
**Uniqueness of minimal realizations**: any two minimal realizations with the
    same behavior are isomorphic (assuming all states are reachable).
-/

/-! ## §14. Closure–Minimization Commutation -/




/-
**Closure–minimization commutation**: when entropy is closure-invariant,
    the original and closure-saturated automata have the same behavior.
-/

/-! ## §15. Dissipation Classes and Conservation -/




/-
**Conservation of dissipation class** for optimal paths of the same length.
-/

/-! ## §16. Certified Minimization -/

/-
**Existence of certified minimization**: the quotient construction provides
    a minimal realization for any thermodynamic automaton.
-/

/-! ## §17. Auxiliary Lemmas -/





/-! ## §18. Closure Invariance -/



open Bridges.AlgebraEMLComputation.IdempotentThermodynamicRealization in
theorem solution[Fintype Q]
    (A : ThermoAut S σ Q) :
    A.gibbsHankelGeneratorRank = Fintype.card (ThermoState A) := by
  -- Show that the image of ther Gibbs–Hankel row function is in bijection with the quotient Q/stateEquiv.
  have h_bij : Nonempty (A.gibbsHankelRows ≃ ThermoState A) := by
    refine' ⟨ Equiv.ofBijective _ ⟨ _, _ ⟩ ⟩;
    refine' fun x => Quotient.mk'' ( Classical.choose ( Finset.mem_image.mp x.2 ) );
    · intro x y hxy
      have h_eq : A.gibbsHankelRow (Classical.choose (Finset.mem_image.mp x.2)) = A.gibbsHankelRow (Classical.choose (Finset.mem_image.mp y.2)) := by
        exact Quotient.exact hxy
      generalize_proofs at *;
      grind +suggestions;
    · intro q;
      obtain ⟨ q, rfl ⟩ := Quotient.exists_rep q;
      refine' ⟨ ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ q ) ⟩, _ ⟩;
      have := Classical.choose_spec ( Finset.mem_image.mp ( show A.gibbsHankelRow q ∈ Finset.image A.gibbsHankelRow Finset.univ from Finset.mem_image_of_mem _ ( Finset.mem_univ q ) ) );
      exact Quotient.sound ( by simpa [ ThermoAut.gibbsHankelRow ] using this.2 );
  simpa using Fintype.card_congr h_bij.some
