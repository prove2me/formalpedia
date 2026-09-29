-- Prove2me | Definitions.Def_Geometry_InformationTheory_HorseshoeComputation
-- name    : Geometry_InformationTheory_HorseshoeComputation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:26:12.000609+00:00
-- url     : https://prove2.me/theorems/86ad822b-465d-4287-a581-042bfa9a1e82
-- title:
--   Aether Catalog definitions — Geometry_InformationTheory_HorseshoeComputation
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.InformationTheory.HorseshoeComputation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/InformationTheory/HorseshoeComputation.lean by skeleton subtraction
import Mathlib

/-!
# Horseshoe Dynamics and Computational Universality

This file formalizes the mathematical chain connecting Smale horseshoe dynamics
to computational universality via symbolic shift spaces.

## Main Definitions

* `SymbolicShift` — The full symbolic shift on `d` symbols
* `Horseshoe` — A map semiconjugate to a full symbolic shift
* `BooleanEncoding` — Encoding of a Boolean function via symbolic itineraries

## Main Results

* `orbit_realization` — Any finite itinerary is realized by an orbit of the full shift
* `boolean_encoding_exists` — Any Boolean function can be encoded by a degree-2 horseshoe
* `entropy_characterization` — Entropy of the full d-shift is log d
* `sub_horseshoe_extraction` — Degree-d contains degree-k sub-horseshoes for k ≤ d
* `horseshoe_iterate_coding` — Semiconjugacy commutes with iteration
-/

noncomputable section

open Function Set Finset

/-! ## Part 1: Symbolic Shift Spaces -/

/-- The full symbolic shift space on `d` symbols: bi-infinite sequences `ℤ → Fin d`. -/
def SymbolicShift (d : ℕ) := ℤ → Fin d

/-- The shift map σ on symbolic sequences: (σx)(n) = x(n+1). -/
def shiftMap (d : ℕ) : SymbolicShift d → SymbolicShift d :=
  fun x n => x (n + 1)

/-
The shift map is injective.
-/

/-
The shift map is surjective.
-/


/-
Iterating the shift map n times gives (σⁿx)(k) = x(k+n).
-/

/-! ## Part 2: Orbit Realization -/

/-- A finite symbolic word of length `n` over `d` symbols. -/
abbrev SymbolicWord (d n : ℕ) := Fin n → Fin d

/-- An orbit of the shift map realizes a word if positions 0..n-1 match the word. -/
def realizesWord (d : ℕ) (x : SymbolicShift d) {n : ℕ} (w : SymbolicWord d n) : Prop :=
  ∀ i : Fin n, x (↑(i : ℕ) : ℤ) = w i

/-
**Orbit Realization Theorem**: Every finite word over `d` symbols is realized by
some orbit of the full shift on `d` symbols.
-/

/-! ## Part 3: Horseshoe Maps -/

/-- A horseshoe structure: a map `f : α → α` with a semiconjugacy to the full d-shift. -/
structure Horseshoe (α : Type*) (d : ℕ) where
  map : α → α
  coding : α → SymbolicShift d
  coding_surjective : Surjective coding
  semiconjugacy : ∀ x, coding (map x) = shiftMap d (coding x)

/-
Iterating a horseshoe map corresponds to iterating the shift via the coding.
-/

/-
A horseshoe map realizes every finite word via its coding.
-/

/-! ## Part 4: Boolean Function Encoding -/

/-- A Boolean function on `n` bits. -/
abbrev BoolFun (n : ℕ) := (Fin n → Bool) → Bool

/-- Encoding of a Boolean function via a symbolic shift. -/
structure BooleanEncoding (d n : ℕ) where
  func : BoolFun n
  boolToSym : Bool → Fin d
  boolToSym_injective : Injective boolToSym
  encoder : (Fin n → Bool) → SymbolicShift d
  encodes_input : ∀ (input : Fin n → Bool) (i : Fin n),
    encoder input (↑(i : ℕ) : ℤ) = boolToSym (input i)
  encodes_output : ∀ (input : Fin n → Bool),
    encoder input (↑n : ℤ) = boolToSym (func input)

/-
**Computational Universality**: For `d ≥ 2`, every Boolean function on `n` bits
can be encoded by the full shift on `d` symbols.
-/

/-! ## Part 5: Sub-horseshoe Extraction -/

/-
**Sub-horseshoe Extraction**: For `k ≤ d`, the full shift on `d` symbols
contains a subsystem conjugate to the full shift on `k` symbols.
-/

/-
The sub-shift space is invariant under the shift map.
-/

/-! ## Part 6: Entropy Bounds -/

/-- The number of distinct words of length `n` in the full shift on `d` symbols. -/
def wordCount (d n : ℕ) : ℕ := d ^ n

/-
**Entropy Characterization**: log(d^n) / n = log d for n > 0.
-/

/-
A subsystem using `k ≤ d` symbols has word count at most `d^n`.
-/

/-! ## Part 7: Parity and Complexity -/

/-- The parity function on n bits. -/
def parityFun (n : ℕ) : BoolFun n :=
  fun input => (Finset.univ.filter (fun i => input i = true)).card % 2 == 0

/-
Parity is nontrivial for n ≥ 1.
-/

/-
**Encoding Monotonicity**: If a function can be encoded with `k` symbols,
it can also be encoded with `d ≥ k` symbols.
-/

end


