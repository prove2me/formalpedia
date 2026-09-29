-- Prove2me | Definitions.Def_Bridges_TropicalAutomatonSpectralRealizationDuality
-- name    : Bridges_TropicalAutomatonSpectralRealizationDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:58.199891+00:00
-- url     : https://prove2.me/theorems/04266b0a-faa3-4db8-8762-9ce7f61a87b4
-- title:
--   Aether Catalog definitions — Bridges_TropicalAutomatonSpectralRealizationDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalAutomatonSpectralRealizationDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalAutomatonSpectralRealizationDuality.lean by skeleton subtraction
import Mathlib
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

namespace TropicalRealization

/-! ## Part 1: Core Definitions -/

/-- A weighted automaton over a commutative semiring `K`, with finite alphabet `A`
and `n` states. States are indexed by `Fin n`. -/
structure WAutomaton (K : Type*) (A : Type*) (n : ℕ) where
  /-- Initial weight vector -/
  init : Fin n → K
  /-- Transition matrices indexed by letters -/
  trans : A → Fin n → Fin n → K
  /-- Output/final weight vector -/
  output : Fin n → K

variable {K : Type*} [CommSemiring K]
variable {A : Type*} [DecidableEq A] [Fintype A]
variable {n m : ℕ}

/-- One-step transition: apply letter `a` to state distribution `v`. -/
def WAutomaton.step (T : WAutomaton K A n) (v : Fin n → K) (a : A) : Fin n → K :=
  fun j => ∑ i : Fin n, v i * T.trans a i j

/-- Reachability vector: state distribution after processing word `w`. -/
def WAutomaton.reach (T : WAutomaton K A n) (w : List A) : Fin n → K :=
  w.foldl T.step T.init

/-- Observation function: weight of processing suffix `v` from state `j`. -/
def WAutomaton.obs (T : WAutomaton K A n) : List A → Fin n → K
  | [] => T.output
  | a :: v => fun j => ∑ i : Fin n, T.trans a j i * T.obs v i

/-- The behavior (recognized series) of a weighted automaton. -/
def WAutomaton.behavior (T : WAutomaton K A n) (w : List A) : K :=
  ∑ j : Fin n, T.reach w j * T.output j

/-- Hankel row of a series `S` at prefix `u`. -/
def hankelRow (S : List A → K) (u : List A) : List A → K :=
  fun v => S (u ++ v)

/-! ## Part 2: Realization Data -/

/-- Realization data: a structured decomposition of a series into `n` generators
with compatible shift structure. This is the algebraic dual of a weighted automaton,
capturing the finite generation and shift stability of the Hankel row semimodule. -/
structure RealizationData (K : Type*) [CommSemiring K] (A : Type*) (n : ℕ) where
  /-- The series being realized -/
  series : List A → K
  /-- Generator functions (one per abstract state) -/
  gen : Fin n → (List A → K)
  /-- Decomposition coefficients -/
  coeff : List A → Fin n → K
  /-- Shift/transition coefficients -/
  shift : A → Fin n → Fin n → K
  /-- Fundamental decomposition: `S(u ++ v) = Σⱼ coeff(u,j) · gen(j)(v)` -/
  decomp : ∀ u v, series (u ++ v) = ∑ j : Fin n, coeff u j * gen j v
  /-- Coefficients shift when a letter is appended -/
  shift_compat : ∀ u (a : A) (j : Fin n),
    coeff (u ++ [a]) j = ∑ i : Fin n, coeff u i * shift a i j
  /-- Generators shift when a letter is prepended -/
  gen_shift : ∀ (a : A) (i : Fin n) (v : List A),
    gen i (a :: v) = ∑ j : Fin n, shift a i j * gen j v

/-! ## Part 3: Forward Realization (Data → Automaton) -/

/-- Construct a weighted automaton from realization data. -/
def RealizationData.toAutomaton (D : RealizationData K A n) : WAutomaton K A n where
  init := D.coeff []
  trans := D.shift
  output := fun j => D.gen j []




/-! ## Part 4: Backward Direction (Automaton → Data) -/


omit [DecidableEq A] [Fintype A] in
/-- Reach after appending a letter applies one step. -/
theorem WAutomaton.reach_snoc (T : WAutomaton K A n) (w : List A) (a : A) :
    T.reach (w ++ [a]) = T.step (T.reach w) a := by
  simp [WAutomaton.reach, List.foldl_append]

omit [DecidableEq A] [Fintype A] in
/-- The reach vector satisfies the shift compatibility condition. -/
theorem WAutomaton.reach_shift_compat (T : WAutomaton K A n)
    (u : List A) (a : A) (j : Fin n) :
    T.reach (u ++ [a]) j = ∑ i : Fin n, T.reach u i * T.trans a i j := by
  simp [reach_snoc, step]

/-
**Fundamental Decomposition Lemma**: the behavior over a concatenation decomposes
via reach and observation vectors.
-/
omit [DecidableEq A] [Fintype A] in
theorem WAutomaton.behavior_decomp (T : WAutomaton K A n) (u v : List A) :
    T.behavior (u ++ v) = ∑ j : Fin n, T.reach u j * T.obs v j := by
  induction' v with v ih generalizing u;
  · aesop;
  · convert ‹∀ u : List A, T.behavior ( u ++ ih ) = ∑ j, T.reach u j * T.obs ih j› ( u ++ [ v ] ) using 1;
    · simp +decide [ List.append_assoc ];
    · simp +decide [ WAutomaton.reach_shift_compat, WAutomaton.obs ];
      simp +decide only [Finset.mul_sum _ _ _, sum_mul, mul_assoc];
      exact Finset.sum_comm

/-- Extract realization data from a weighted automaton. Every `n`-state automaton
canonically yields realization data of rank `n`. -/
noncomputable def WAutomaton.toRealizationData (T : WAutomaton K A n) :
    RealizationData K A n where
  series := T.behavior
  gen := fun j v => T.obs v j
  coeff := T.reach
  shift := T.trans
  decomp := T.behavior_decomp
  shift_compat := fun u a j => T.reach_shift_compat u a j
  gen_shift := fun a i v => by simp [obs]

/-! ## Part 5: Realization Duality -/

/-- A series is **realizable** by an `n`-state automaton. -/
def IsRealizable (S : List A → K) (n : ℕ) : Prop :=
  ∃ T : WAutomaton K A n, T.behavior = S


/-! ## Part 6: Reachability, Observability, Minimality -/


/-- An automaton is **observable** if distinct states produce distinct
observation vectors. -/
def WAutomaton.IsObservable (T : WAutomaton K A n) : Prop :=
  ∀ i j : Fin n, (∀ v : List A, T.obs v i = T.obs v j) → i = j




/-! ## Part 7: Automaton Isomorphism and Uniqueness -/

/-- An isomorphism between two weighted automata: a bijection on state sets
that preserves all automaton structure (initial weights, transitions, outputs). -/
structure WAutomatonIso (T₁ : WAutomaton K A n) (T₂ : WAutomaton K A m) where
  /-- Bijection between state spaces -/
  stateEquiv : Fin n ≃ Fin m
  /-- Initial weights are preserved -/
  init_compat : ∀ i, T₂.init (stateEquiv i) = T₁.init i
  /-- Transition weights are preserved -/
  trans_compat : ∀ (a : A) (i j : Fin n),
    T₂.trans a (stateEquiv i) (stateEquiv j) = T₁.trans a i j
  /-- Output weights are preserved -/
  output_compat : ∀ j, T₂.output (stateEquiv j) = T₁.output j




/-
**Observation Matching Equivalence**: Given a unique observational matching
between states of two automata with the same number of states, there exists
a state bijection preserving all observation vectors and output weights.
-/


/-! ## Part 8: Certified Reconstruction -/

/-- A **Hankel window certificate** attests that a finite observation window
suffices to determine a generating family for the Hankel row semimodule,
enabling certified reconstruction of a minimal weighted automaton. -/
structure HankelWindowCert (K : Type*) [CommSemiring K] (A : Type*) (n : ℕ) where
  /-- The series to be realized -/
  series : List A → K
  /-- Witness prefixes (one per generator) -/
  prefixes : Fin n → List A
  /-- Test suffixes -/
  suffixes : Finset (List A)
  /-- Generator functions -/
  gen : Fin n → (List A → K)
  /-- Decomposition coefficients -/
  coeff : List A → Fin n → K
  /-- Shift coefficients -/
  shift : A → Fin n → Fin n → K
  /-- The window data yields a full decomposition -/
  window_consistent : ∀ u v, series (u ++ v) = ∑ j : Fin n, coeff u j * gen j v
  /-- Shift compatibility -/
  shift_verified : ∀ u (a : A) (j : Fin n),
    coeff (u ++ [a]) j = ∑ i : Fin n, coeff u i * shift a i j
  /-- Generator shift compatibility -/
  gen_shift_verified : ∀ (a : A) (i : Fin n) (v : List A),
    gen i (a :: v) = ∑ j : Fin n, shift a i j * gen j v

/-- Extract realization data from a Hankel window certificate. -/
def HankelWindowCert.toRealizationData (C : HankelWindowCert K A n) :
    RealizationData K A n where
  series := C.series
  gen := C.gen
  coeff := C.coeff
  shift := C.shift
  decomp := C.window_consistent
  shift_compat := C.shift_verified
  gen_shift := C.gen_shift_verified


/-! ## Part 9: Hankel Row Characterization -/



end TropicalRealization


