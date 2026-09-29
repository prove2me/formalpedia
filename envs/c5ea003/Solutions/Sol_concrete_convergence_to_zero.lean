-- Prove2me | solution 1 for concrete_convergence_to_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:47:00.133219+00:00
-- url     : https://prove2.me/submissions/bdce3dca-559b-48d9-bad9-53871a774ecc

-- Sol generated from Bridges/TropicalDeSitterCTheorem.lean
import Mathlib
import Definitions.Def_Bridges_TropicalDeSitterCTheorem
/-
# Tropical de Sitter Entropic c-Theorem via Idempotent Transfer Renormalization
  and Closure Horizon Capacities

## Overview

This module formalizes a **tropical cosmological renormalization** framework:
a certified min-plus monotonicity theorem with exact fixed-point rigidity and
functorial entropy-loss bounds for finite idempotent transfer systems equipped
with closure operators and horizon-capacity corrections.

## Core Results

- **Theorem A** (`canonical_rg_closure_compatible`, `canonical_rg_iterates_closed`):
  The canonical RG operator Krg := Cl ∘ K ∘ Cl preserves closure saturation.

- **Theorem B** (`rg_monotone_energy_and_capacity`, `cfun_monotone_along_rg`):
  A closure-corrected tropical c-function is monotone decreasing along RG flow.

- **Theorem C** (`cfun_equality_iff_equilibrium`):
  Equality in the c-theorem characterizes idempotent transfer equilibrium.

- **Theorem D** (`rg_natural`, `cfun_monotone_under_morphism`):
  RG dynamics is natural under closure-compatible morphisms, and c-function
  bounds transfer functorially across coarse-graining maps.

## Keywords

tropical renormalization group, min-plus c-theorem, de Sitter entropy,
horizon capacity, idempotent transfer dynamics, EML closure,
closure-compatible coarse-graining, tropical free energy, cycle-mean monotonicity,
entropy-loss certification, irreversible information flow, categorical RG,
tropical thermodynamics, finite-state cosmological dynamics
-/


open Function

/-! ## Section 1: Closure Operator Basics -/




/-! ## Section 2: Transfer Equilibrium -/


/-! ## Section 3: Canonical RG Operator -/


/-! ## Theorem A: Closure Saturation of the RG Operator -/



/-! ## Section 4: Monotonicity of the RG Operator -/


/-! ## Theorem B: Monotonicity of the c-Function -/




/-! ## Theorem C: Fixed-Point Rigidity / Equilibrium Characterization -/





/-! ## Section 5: Functorial Structure -/


/-! ## Theorem D: Naturality and Functorial c-Function Bounds -/




/-! ## Section 6: Concrete Instantiation with ℕ-valued functions -/


variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]






/-
After one RG step with halfTransfer and maxClosure, the max energy decreases.
    This is the concrete c-theorem: the tropical spectral radius cannot increase
    under coarse-graining.
-/

/-
The RG orbit converges to a constant function after one step.
-/

/-
The zero function is a transfer equilibrium.
-/

/-
Convergence: the RG orbit reaches the zero equilibrium in finitely many steps.
-/


-- open removed: section is not a namespace
omit [DecidableEq X] in
theorem solution(f : X → ℕ) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      (canonicalRG halfTransfer (maxClosure (X := X)))^[n] f = fun _ => 0 := by
  -- Let M be the maximum value of f.
  set M := Finset.univ.sup' Finset.univ_nonempty f with hM_def
  generalize_proofs at *; (
  -- By induction on $M$, we can show that after at most $\log_2(M) + 1$ steps, the function becomes zero.
  have h_induction : ∀ m, ∀ f : X → ℕ, (Finset.univ.sup' Finset.univ_nonempty f) ≤ m → ∃ N, ∀ n ≥ N, (canonicalRG halfTransfer maxClosure)^[n] f = fun _ => 0 := by
    intro m
    generalize_proofs at *; (
    induction' m with m ih <;> simp_all +decide [ Function.iterate_succ_apply' ];
    · intro f hf; use 0; intro n hn; induction hn <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
      · exact funext hf;
      · unfold canonicalRG halfTransfer maxClosure; aesop;
    · intro f hf
      obtain ⟨N, hN⟩ := ih (fun x => (canonicalRG halfTransfer maxClosure) f x) (by
      simp +decide [ canonicalRG, halfTransfer, maxClosure ];
      exact Nat.le_of_lt_succ ( Nat.div_lt_of_lt_mul <| by linarith [ show Finset.univ.sup' ( by assumption ) f ≤ m + 1 from Finset.sup'_le _ _ fun x _ => hf x ] ));
      exact ⟨ N + 1, fun n hn => by simpa only [ ← Function.iterate_succ_apply' ] using hN ( n - 1 ) ( Nat.le_sub_one_of_lt hn ) |> fun h => by cases n <;> tauto ⟩)
  generalize_proofs at *; (
  exact h_induction M f le_rfl))
