-- Prove2me | solution 1 for TropicalRealization.WAutomatonIso.behavior_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:07:32.035919+00:00
-- url     : https://prove2.me/submissions/966785da-adf1-4e50-933d-3f5bf8a35bd1

-- Sol generated from Bridges/TropicalAutomatonSpectralRealizationDuality.lean
import Mathlib
import Definitions.Def_Bridges_TropicalAutomatonSpectralRealizationDuality
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Automaton Spectral Realization Duality

This file establishes a **realization duality theorem** for weighted automata over
commutative semirings, with particular application to idempotent (tropical) semirings.

## Main Results

* `RealizationData.behavior_eq` — A finitely generated shift-stable Hankel decomposition
  yields a weighted automaton whose behavior equals the original series.
* `WAutomaton.toRealizationData` — Every finite weighted automaton induces a finite
  Hankel realization data structure.
* `realization_duality` — A series admits realization data of rank `n` if and only if
  it is realizable by an `n`-state weighted automaton.
* `minimalRealization_unique` — Two reachable-observable minimal realizations with the
  same behavior are isomorphic as weighted automata.
* `certified_reconstruction` — From a Hankel window certificate of rank `n`,
  one can reconstruct a minimal weighted automaton realizing the series.

## Mathematical Context

This formalizes the tropical analogue of the Schützenberger–Fliess realization theorem.
Classical Schützenberger/Fliess theory states that a formal power series over a field is
recognizable (i.e., realized by a finite weighted automaton) if and only if its Hankel
matrix has finite rank. In the tropical/idempotent setting, the correct invariant is
**finite generation of the Hankel row semimodule** together with shift stability.

## Keywords

tropical automata, weighted transducers, idempotent semimodules, Hankel realization,
recognizable series, Schützenberger theory, Fliess realization, certified reconstruction,
automata minimization, tropical system identification
-/

open Finset BigOperators

open TropicalRealization

/-! ## Part 1: Core Definitions -/


variable {K : Type*} [CommSemiring K]
variable {A : Type*} [DecidableEq A] [Fintype A]
variable {n m : ℕ}






/-! ## Part 2: Realization Data -/


/-! ## Part 3: Forward Realization (Data → Automaton) -/





/-! ## Part 4: Backward Direction (Automaton → Data) -/




/-
**Fundamental Decomposition Lemma**: the behavior over a concatenation decomposes
via reach and observation vectors.
-/


/-! ## Part 5: Realization Duality -/



/-! ## Part 6: Reachability, Observability, Minimality -/






/-! ## Part 7: Automaton Isomorphism and Uniqueness -/





/-
**Observation Matching Equivalence**: Given a unique observational matching
between states of two automata with the same number of states, there exists
a state bijection preserving all observation vectors and output weights.
-/


/-! ## Part 8: Certified Reconstruction -/




/-! ## Part 9: Hankel Row Characterization -/




open TropicalRealization in
omit [DecidableEq A] [Fintype A] in
theorem solution{T₁ : WAutomaton K A n} {T₂ : WAutomaton K A m}
    (iso : WAutomatonIso T₁ T₂) : T₁.behavior = T₂.behavior := by
  -- By definition of behavior, we have:
  funext w
  simp [WAutomaton.behavior];
  -- By definition of reach, we have:
  have h_reach : ∀ w : List A, ∀ j : Fin n, T₁.reach w j = T₂.reach w (iso.stateEquiv j) := by
    intro w j;
    induction' w using List.reverseRecOn with w a ih generalizing j <;> simp_all +decide [ WAutomaton.reach ];
    · exact iso.init_compat j ▸ rfl;
    · simp +decide [ WAutomaton.step, ih ];
      refine' Finset.sum_bij ( fun i _ => iso.stateEquiv i ) _ _ _ _ <;> simp +decide [ iso.trans_compat ];
      exact iso.stateEquiv.surjective;
  rw [ ← Equiv.sum_comp iso.stateEquiv ] ; simp +decide [ h_reach, iso.output_compat ] ;
