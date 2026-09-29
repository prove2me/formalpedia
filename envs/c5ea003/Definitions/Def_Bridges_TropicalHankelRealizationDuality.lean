-- Prove2me | Definitions.Def_Bridges_TropicalHankelRealizationDuality
-- name    : Bridges_TropicalHankelRealizationDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:25.947195+00:00
-- url     : https://prove2.me/theorems/14f8c48d-ce3d-4104-821a-26efa9fe6bd1
-- title:
--   Aether Catalog definitions — Bridges_TropicalHankelRealizationDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalHankelRealizationDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalHankelRealizationDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Hankel Realization Duality

A min-plus weighted analogue of the Schützenberger–Hankel theorem establishing that
**recognizability, finite residual generation, finite tropical Hankel rank, and
certified minimal realization all coincide** for weighted languages over commutative
semirings (with particular application to tropical/idempotent semirings).

## Main Results

* `recognizable_iff_fg_hankel_row` — Recognizability ↔ finitely generated Hankel rows
  with shift stability (the Schützenberger–Fliess realization theorem).
* `recognizable_implies_fg_residual` — Recognizability implies finitely generated residuals.
* `recognizable_implies_finite_hankel_rank` — Recognizability implies finite Hankel rank.
* `certified_reconstruction` — From a Hankel window certificate, reconstruct an automaton.
* `obs_matching_of_same_behavior` — Observable automata with matched observations
  produce an isomorphism.

## Mathematical Context

This formalizes the tropical analogue of the Schützenberger–Fliess–Carlyle–Paz
realization theorem. The correct invariant for recognizability is **finite generation
of the Hankel row semimodule** together with shift stability.

## Keywords

tropical automata, min-plus semiring, Hankel realization, Schützenberger theorem,
weighted languages, residual semimodule, tropical factor rank, automata minimization,
certified reconstruction, canonical realization
-/

open Finset BigOperators

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace TropicalHankelRealization

/-! ## §1. Core Definitions -/

structure WAutomaton (K : Type*) (A : Type*) (n : ℕ) where
  init : Fin n → K
  trans : A → Fin n → Fin n → K
  output : Fin n → K

variable {K : Type*} [CommSemiring K]
variable {A : Type*} [DecidableEq A] [Fintype A]
variable {n m : ℕ}

def WAutomaton.step (T : WAutomaton K A n) (v : Fin n → K) (a : A) : Fin n → K :=
  fun j => ∑ i : Fin n, v i * T.trans a i j

def WAutomaton.reach (T : WAutomaton K A n) (w : List A) : Fin n → K :=
  w.foldl T.step T.init

def WAutomaton.obs (T : WAutomaton K A n) : List A → Fin n → K
  | [] => T.output
  | a :: v => fun j => ∑ i : Fin n, T.trans a j i * T.obs v i

def WAutomaton.behavior (T : WAutomaton K A n) (w : List A) : K :=
  ∑ j : Fin n, T.reach w j * T.output j

def WAutomaton.stateCount (_ : WAutomaton K A n) : ℕ := n

/-! ## §2. Residuals and Hankel -/

def leftResidual (L : List A → K) (u : List A) : List A → K :=
  fun v => L (u ++ v)


def hankel (L : List A → K) (u v : List A) : K := L (u ++ v)

def hankelRow (L : List A → K) (u : List A) : List A → K :=
  fun v => L (u ++ v)


/-! ## §3. Recognizability and Finite Generation -/

def RecognizableTropLanguage (L : List A → K) : Prop :=
  ∃ (n : ℕ) (T : WAutomaton K A n), T.behavior = L

def FGResidualSemimodule (L : List A → K) : Prop :=
  ∃ (n : ℕ) (gen : Fin n → (List A → K)),
    ∀ u : List A, ∃ c : Fin n → K,
      ∀ v : List A, L (u ++ v) = ∑ j : Fin n, c j * gen j v

def FGHankelRowSemimodule (L : List A → K) : Prop :=
  ∃ (n : ℕ) (gen : Fin n → (List A → K))
    (coeff : List A → Fin n → K)
    (shift : A → Fin n → Fin n → K),
    (∀ u v, L (u ++ v) = ∑ j : Fin n, coeff u j * gen j v) ∧
    (∀ u (a : A) (j : Fin n),
      coeff (u ++ [a]) j = ∑ i : Fin n, coeff u i * shift a i j) ∧
    (∀ (a : A) (i : Fin n) (v : List A),
      gen i (a :: v) = ∑ j : Fin n, shift a i j * gen j v)

structure RealizationData (K : Type*) [CommSemiring K] (A : Type*) (n : ℕ) where
  series : List A → K
  gen : Fin n → (List A → K)
  coeff : List A → Fin n → K
  shift : A → Fin n → Fin n → K
  decomp : ∀ u v, series (u ++ v) = ∑ j : Fin n, coeff u j * gen j v
  shift_compat : ∀ u (a : A) (j : Fin n),
    coeff (u ++ [a]) j = ∑ i : Fin n, coeff u i * shift a i j
  gen_shift : ∀ (a : A) (i : Fin n) (v : List A),
    gen i (a :: v) = ∑ j : Fin n, shift a i j * gen j v

def TropicalHankelFactorRankAtMost (L : List A → K) (n : ℕ) : Prop :=
  ∃ (gen : Fin n → (List A → K)) (coeff : List A → Fin n → K),
    ∀ u v, L (u ++ v) = ∑ j : Fin n, coeff u j * gen j v

/-! ## §4. Forward Realization: Data → Automaton -/

def RealizationData.toAutomaton (D : RealizationData K A n) : WAutomaton K A n where
  init := D.coeff []
  trans := D.shift
  output := fun j => D.gen j []




/-! ## §5. Backward Direction: Automaton → Data -/


omit [DecidableEq A] [Fintype A] in
theorem WAutomaton.reach_snoc (T : WAutomaton K A n) (w : List A) (a : A) :
    T.reach (w ++ [a]) = T.step (T.reach w) a := by
  simp [WAutomaton.reach, List.foldl_append]

omit [DecidableEq A] [Fintype A] in
theorem WAutomaton.reach_shift_compat (T : WAutomaton K A n)
    (u : List A) (a : A) (j : Fin n) :
    T.reach (u ++ [a]) j = ∑ i : Fin n, T.reach u i * T.trans a i j := by
  simp [reach_snoc, step]

omit [DecidableEq A] [Fintype A] in
theorem WAutomaton.behavior_decomp (T : WAutomaton K A n) (u v : List A) :
    T.behavior (u ++ v) = ∑ j : Fin n, T.reach u j * T.obs v j := by
  induction' v with v ih generalizing u;
  · aesop;
  · simp_all +decide [ WAutomaton.reach_snoc, WAutomaton.step, WAutomaton.step, WAutomaton.obs ];
    convert ‹∀ u : List A, T.behavior ( u ++ ih ) = ∑ j, T.reach u j * T.obs ih j› ( u ++ [ v ] ) using 1;
    · simp +decide [ List.append_assoc ];
    · simp +decide [ WAutomaton.reach_snoc, WAutomaton.step, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.sum_mul ];
      exact Finset.sum_comm

noncomputable def WAutomaton.toRealizationData (T : WAutomaton K A n) :
    RealizationData K A n where
  series := T.behavior
  gen := fun j v => T.obs v j
  coeff := T.reach
  shift := T.trans
  decomp := T.behavior_decomp
  shift_compat := fun u a j => T.reach_shift_compat u a j
  gen_shift := fun a i v => by simp [obs]

/-! ## §6. Realization Duality -/


/-! ## §7. Recognizable ↔ FGHankelRowSemimodule -/





/-! ## §8. Hankel Factor Rank -/



/-! ## §9. Automaton Isomorphism -/

structure WAutomatonIso (T₁ : WAutomaton K A n) (T₂ : WAutomaton K A m) where
  stateEquiv : Fin n ≃ Fin m
  init_compat : ∀ i, T₂.init (stateEquiv i) = T₁.init i
  trans_compat : ∀ (a : A) (i j : Fin n),
    T₂.trans a (stateEquiv i) (stateEquiv j) = T₁.trans a i j
  output_compat : ∀ j, T₂.output (stateEquiv j) = T₁.output j


def WAutomaton.IsObservable (T : WAutomaton K A n) : Prop :=
  ∀ i j : Fin n, (∀ v : List A, T.obs v i = T.obs v j) → i = j





/-! ## §10. Residual Shift Closure -/



/-! ## §11. Finite Hankel Generation -/



/-! ## §12. Certified Reconstruction -/

structure HankelWindowCert (K : Type*) [CommSemiring K] (A : Type*) (n : ℕ) where
  series : List A → K
  gen : Fin n → (List A → K)
  coeff : List A → Fin n → K
  shift : A → Fin n → Fin n → K
  window_consistent : ∀ u v, series (u ++ v) = ∑ j : Fin n, coeff u j * gen j v
  shift_verified : ∀ u (a : A) (j : Fin n),
    coeff (u ++ [a]) j = ∑ i : Fin n, coeff u i * shift a i j
  gen_shift_verified : ∀ (a : A) (i : Fin n) (v : List A),
    gen i (a :: v) = ∑ j : Fin n, shift a i j * gen j v

def HankelWindowCert.toRealizationData (C : HankelWindowCert K A n) :
    RealizationData K A n where
  series := C.series
  gen := C.gen
  coeff := C.coeff
  shift := C.shift
  decomp := C.window_consistent
  shift_compat := C.shift_verified
  gen_shift := C.gen_shift_verified

def HankelWindowCert.toAutomaton (C : HankelWindowCert K A n) : WAutomaton K A n :=
  C.toRealizationData.toAutomaton


/-! ## §13. Observation Matching for Uniqueness -/



/-! ## §14. State Count Bounds -/

def IsRealizable (S : List A → K) (n : ℕ) : Prop :=
  ∃ T : WAutomaton K A n, T.behavior = S


/-! ## §15. Summary Theorems -/






/-! ## §16. Tropical Specialization -/

/-- The min-plus tropical semiring type. -/
abbrev Trop := Tropical (WithTop ℕ)

abbrev TropLanguage (A : Type*) := List A → Trop



end TropicalHankelRealization


