-- Prove2me | solution 1 for Bridges.AlgebraEMLComputation.IdempotentThermodynamicRealization.ThermoAut.minimal_realization_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T13:42:32.801657+00:00
-- url     : https://prove2.me/submissions/43266ced-c840-4c01-bf35-61f8fc507077

-- Sol generated from Bridges/IdempotentThermodynamicRealization.lean
import Mathlib
import Definitions.Def_Bridges_IdempotentThermodynamicRealization
import Theorems.Thm_Bridges_AlgebraEMLComputation_IdempotentThermodynamicRealization_ThermoAut_quotientAut_minimal
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
  | nil => simp [ThermoAut.run]
  | cons a u ih => simp [ThermoAut.run, ih]

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
    [Fintype Q] [Fintype Q'] [DecidableEq Q] [DecidableEq Q']
    (A : ThermoAut S σ Q) (B : ThermoAut S σ Q')
    (hA : A.IsMinimalRealization) (hB : B.IsMinimalRealization)
    (hbeh : A.behavior = B.behavior)
    (hA_surj : ∀ q : Q, ∃ w, A.run A.init w = q)
    (hB_surj : ∀ q : Q', ∃ w, B.run B.init w = q) :
    Nonempty (ThermoAutIso A B) := by
  -- Construct the isomorphism f : Q ≃ Q' as follows.
  have h_iso : Nonempty (Q ≃ Q') := by
    have h_card : Fintype.card Q = Fintype.card (ThermoState A) := by
      refine' Fintype.card_congr _;
      refine' Equiv.ofBijective ( fun q => Quotient.mk'' q ) ⟨ fun q₁ q₂ h => _, fun q => _ ⟩ <;> simp_all +decide [ ThermoAut.stateEquiv ];
      · exact hA _ _ ( Quotient.exact h );
      · exact Quotient.exists_rep q
    have h_card' : Fintype.card Q' = Fintype.card (ThermoState B) := by
      refine' Fintype.card_congr _;
      refine' Equiv.ofBijective ( fun q => Quotient.mk'' q ) ⟨ fun q₁ q₂ h => _, fun q => _ ⟩;
      · exact hB _ _ ( Quotient.exact h );
      · exact Quotient.exists_rep q
    have h_card_eq : Fintype.card (ThermoState A) = Fintype.card (ThermoState B) := by
      have h_card_eq : Fintype.card (ThermoState A) ≤ Fintype.card Q' := by
        apply ThermoAut.quotientAut_minimal A B hbeh hA_surj
      have h_card_eq' : Fintype.card (ThermoState B) ≤ Fintype.card Q := by
        apply ThermoAut.quotientAut_minimal B A (by
        exact hbeh.symm) (by
        exact hB_surj)
      linarith [h_card_eq, h_card_eq']
    have h_card_eq' : Fintype.card Q = Fintype.card Q' := by
      rw [h_card, h_card', h_card_eq]
    exact ⟨Fintype.equivOfCardEq h_card_eq'⟩;
  -- Define the function f that maps each state in A to the corresponding state in B.
  obtain ⟨f, hf⟩ : ∃ f : Q ≃ Q', ∀ q, A.residual q = B.residual (f q) := by
    have h_iso : ∀ q : Q, ∃ q' : Q', A.residual q = B.residual q' := by
      intro q
      obtain ⟨w, hw⟩ := hA_surj q
      use B.run B.init w;
      ext x; have := congr_fun hbeh ( w ++ x ) ; simp_all +decide [ ThermoAut.behavior ] ;
      convert this using 1 <;> simp +decide [ ← hw, ThermoAut.residual ];
      · rw [ ThermoAut.run_append ];
      · rw [ ThermoAut.run_append ];
    choose f hf using h_iso;
    have h_inj : Function.Injective f := by
      intro q₁ q₂ h_eq
      have h_res : A.residual q₁ = A.residual q₂ := by
        rw [ hf q₁, hf q₂, h_eq ];
      exact hA q₁ q₂ h_res;
    have h_surj : Function.Surjective f := by
      exact ( Fintype.bijective_iff_injective_and_card f ).mpr ⟨ h_inj, by simp +decide [ Fintype.card_congr h_iso.some ] ⟩ |>.2;
    exact ⟨ Equiv.ofBijective f ⟨ h_inj, h_surj ⟩, hf ⟩;
  refine' ⟨ ⟨ f, _, _, _ ⟩ ⟩;
  · have h_init : A.residual A.init = B.residual B.init := by
      convert hbeh using 1;
    have := hB ( f A.init ) B.init; aesop;
  · intro q a
    have hgoal : A.step q a = f.symm (B.step (f q) a) := by
      apply hA
      rw [ThermoAut.stateEquiv_iff]
      intro w
      have e1 : A.obs (A.run (A.step q a) w) = B.obs (B.run (f q) (a :: w)) := by
        rw [show A.run (A.step q a) w = A.run q (a :: w) from rfl]
        exact congr_fun (hf q) (a :: w)
      have e2 : A.obs (A.run (f.symm (B.step (f q) a)) w)
          = B.obs (B.run (B.step (f q) a) w) := by
        conv_rhs => rw [← Equiv.apply_symm_apply f (B.step (f q) a)]
        exact congr_fun (hf (f.symm (B.step (f q) a))) w
      rw [e1, e2]
      rfl
    rw [hgoal]
    exact Equiv.apply_symm_apply f (B.step (f q) a)
  · intro q
    have h0 := congr_fun (hf q) []
    simpa only [ThermoAut.residual, ThermoAut.run] using h0
