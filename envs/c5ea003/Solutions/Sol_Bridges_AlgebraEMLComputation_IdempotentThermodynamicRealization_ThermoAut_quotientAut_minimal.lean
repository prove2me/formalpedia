-- Prove2me | solution 1 for Bridges.AlgebraEMLComputation.IdempotentThermodynamicRealization.ThermoAut.quotientAut_minimal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T13:40:40.673611+00:00
-- url     : https://prove2.me/submissions/14f4fc00-d871-4cfa-8349-121774e01f0e

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




/-- Running on a concatenation equals running sequentially. -/
theorem ThermoAut.run_append (A : ThermoAut S σ Q) (q : Q) (u v : List σ) :
    A.run q (u ++ v) = A.run (A.run q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih =>
    show A.run (A.step q a) (u ++ v) = A.run (A.run (A.step q a) u) v
    rw [ih]

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
theorem solution{Q' : Type*}
    [Fintype Q] [Fintype Q']
    (A : ThermoAut S σ Q) (B : ThermoAut S σ Q')
    (hbeh : A.behavior = B.behavior)
    (hA_surj : ∀ q : Q, ∃ w, A.run A.init w = q) :
    Fintype.card (ThermoState A) ≤ Fintype.card Q' := by
  -- The set of A-residuals (image of A.residual on Q) is contained in the set of B-residuals (image of B.residual on Q').
  have h_image_subset : Set.range (fun q : Q => A.residual q) ⊆ Set.range (fun q : Q' => B.residual q) := by
    rintro _ ⟨ q, rfl ⟩;
    obtain ⟨ w, rfl ⟩ := hA_surj q;
    use B.run B.init w;
    ext x;
    simp_all +decide [ funext_iff, ThermoAut.residual, ThermoAut.behavior ];
    convert hbeh ( w ++ x ) |> Eq.symm using 1;
    · rw [ ThermoAut.run_append ];
    · rw [ ThermoAut.run_append ];
  have h_card_image : Fintype.card (ThermoState A) = Set.ncard (Set.range (fun q : Q => A.residual q)) := by
    rw [ Set.ncard_eq_toFinset_card' ];
    refine' Finset.card_bij ( fun q _ => A.residual ( Quotient.out q ) ) _ _ _ <;> simp +decide;
    · intro a₁ a₂ h; rw [ ← Quotient.out_eq a₁, ← Quotient.out_eq a₂ ] ; exact Quotient.sound h;
    · intro q;
      have := Quotient.out_eq' ( ⟦q⟧ : Quotient A.stateSetoid );
      erw [ Quotient.eq ] at this ; aesop;
  exact h_card_image ▸ le_trans ( Set.ncard_le_ncard h_image_subset ) ( by rw [ Set.ncard_eq_toFinset_card _ ] ; simpa using Finset.card_image_le )
