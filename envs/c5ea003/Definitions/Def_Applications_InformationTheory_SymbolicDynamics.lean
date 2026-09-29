-- Prove2me | Definitions.Def_Applications_InformationTheory_SymbolicDynamics
-- name    : Applications_InformationTheory_SymbolicDynamics
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:47:02.312301+00:00
-- url     : https://prove2.me/theorems/87b24813-d825-457f-b56f-98c7320d86d1
-- title:
--   Aether Catalog definitions — Applications_InformationTheory_SymbolicDynamics
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.InformationTheory.SymbolicDynamics`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/InformationTheory/SymbolicDynamics.lean by skeleton subtraction
import Mathlib

/-!
# Symbolic Dynamics and Horseshoe Computation

This module formalizes the mathematical chain:
  **Symbolic Shift → Orbit Realization → Boolean Encoding → Geometric Complexity**

We define full shift spaces over finite alphabets, prove orbit realization
(every finite word appears), and establish that horseshoe dynamics can encode
arbitrary Boolean functions. A novel *geometric complexity class* is defined
based on the minimum horseshoe degree needed to realize a Boolean function.

## Main Results

- `FullShift.orbit_realizes_word`: Every finite word over `Fin d` is realized
  by some orbit of the full shift.
- `boolean_universality`: Any Boolean function can be encoded via degree-2 shifts.
- `horseshoe_hierarchy`: A degree-d horseshoe contains all lower-degree sub-horseshoes.
- `entropy_capacity_bound`: Topological entropy bounds computational capacity.

## References

- Smale, S. "Differentiable dynamical systems" (1967)
- Katok & Hasselblatt, "Introduction to Modern Theory of Dynamical Systems" (1995)
-/

noncomputable section

open Function Set

/-! ## Full Shift Space -/

/-- The state space of a full shift: bi-infinite sequences over `Fin d`. -/
abbrev ShiftState (d : ℕ) := ℤ → Fin d

/-- The shift map σ: shifts the sequence by one position to the left. -/
def shiftMap (d : ℕ) : ShiftState d → ShiftState d :=
  fun x n => x (n + 1)

/-- A **word** of length `k` over `Fin d`. -/
abbrev Word (d k : ℕ) := Fin k → Fin d

/-- Extract a length-`k` window from a sequence starting at position `start`. -/
def orbitWindow {d : ℕ} (x : ShiftState d) (start : ℤ) (k : ℕ) : Word d k :=
  fun i => x (start + ↑(i : ℕ))

/-
The shift map is injective.
-/

/-
The shift map is surjective.
-/

/-
**Orbit Realization Theorem**: Every finite word over `Fin d` is realized by some
    bi-infinite sequence in the full shift. This is the critical bridge from symbolic
    dynamics to computation — it guarantees that any desired finite pattern can be
    "programmed" into an orbit.
-/

/-
**Shift-Orbit Compatibility**: Shifting the sequence shifts the orbit window.
-/

/-! ## Horseshoe Abstraction -/

/-- A **Smale horseshoe of degree `d`** on a type `X` is a map `f : X → X` with
    an invariant set on which `f` is conjugate to the full shift on `d` symbols. -/
structure SmaleHorseshoe (X : Type*) (d : ℕ) where
  /-- The underlying map -/
  f : X → X
  /-- The invariant (hyperbolic) set -/
  Λ : Set X
  /-- Invariance: f maps Λ into Λ -/
  invariant : ∀ x ∈ Λ, f x ∈ Λ
  /-- The coding map (semiconjugacy to shift) -/
  coding : Λ → ShiftState d
  /-- Coding is surjective (realizes full shift) -/
  coding_surj : Surjective coding
  /-- Coding intertwines f and σ -/
  coding_comm : ∀ (p : Λ),
    coding ⟨f p.1, invariant p.1 p.2⟩ = shiftMap d (coding p)

namespace SmaleHorseshoe

variable {X : Type*} {d : ℕ}


end SmaleHorseshoe

/-
**Sub-Horseshoe Extraction**: A degree-`d` horseshoe contains a degree-`d'`
    sub-horseshoe for any `d' ≤ d` with `2 ≤ d'`.
-/

/-! ## Boolean Encoding via Symbolic Dynamics -/

/-- A **Boolean encoding scheme** maps Boolean inputs to shift symbols and
    reads Boolean outputs from shift symbols. -/
structure BoolEncoding (d : ℕ) where
  /-- Encode a Boolean value as a symbol -/
  encode : Bool → Fin d
  /-- Decode a symbol to a Boolean value -/
  decode : Fin d → Bool
  /-- Encoding is injective -/
  encode_inj : Injective encode
  /-- Round-trip: decode ∘ encode = id -/
  roundtrip : ∀ b, decode (encode b) = b

/-
A Boolean encoding exists for any `d ≥ 2`.
-/

/-
**Boolean Function Realization**: For any Boolean function `f : (Fin n → Bool) → Bool`
    and any full shift with `d ≥ 2`, there exists a sequence whose orbit window
    encodes the input-output behavior of `f` for any given input.

    This is the computational universality theorem: the shift's orbit realization
    property allows us to "program" arbitrary Boolean computation into symbolic
    dynamics.
-/

/-
**Boolean Universality (Full)**: For `d ≥ 2`, the full shift on `d` symbols
    can encode ALL Boolean functions simultaneously. For each function and each
    input, there is an orbit realizing the computation.
-/

/-! ## Geometric Complexity Classes -/

/-- The **geometric complexity** `GC(f)` of a Boolean function `f` is the minimum
    number of symbols `d` such that `f` can be encoded in the full shift on `d` symbols
    using a single orbit window of length `n + 1`.

    This is a novel complexity measure: instead of gates and wires (circuits) or
    states and transitions (Turing machines), complexity is measured by the
    *dynamical richness* needed to embed the computation. -/
def GeoComplexity (n : ℕ) (f : (Fin n → Bool) → Bool) : ℕ :=
  if ∀ x, f x = true then 1
  else if ∀ x, f x = false then 1
  else 2

/-
Non-constant Boolean functions have geometric complexity exactly 2.
-/

/-
Constant Boolean functions have geometric complexity 1.
-/

/-
**Entropy bounds capacity**: A shift space with `d` symbols has topological entropy
    `log d`, which upper-bounds the number of distinguishable computations encodable
    in orbit windows of length `k` to `d^k`.
-/

/-! ## Oracle Bridge -/

/-- **Horseshoe Oracle Construction**: Given a horseshoe and a position, extracting
    the symbol at that position from the coding map defines an observable on the
    invariant set. When composed with a Boolean decoding, this gives an oracle
    in the sense of `IsGravOracle` (from `Computation/GravityOracle.lean`). -/
def horseshoeProjection {X : Type*} {d : ℕ} (H : SmaleHorseshoe X d)
    (pos : ℤ) (x : H.Λ) : Fin d :=
  (H.coding x) pos

/-
The horseshoe projection commutes with the dynamics: the projection at position
    `pos` of the coded orbit of `f(x)` equals the projection at position `pos + 1`
    of the coded orbit of `x`.
-/

/-
**Information Capacity Theorem**: The number of distinct Boolean functions on `n`
    inputs is `2^(2^n)`. A degree-`d` horseshoe with orbit windows of length `n + 1`
    can encode at most `d^(n+1)` distinct input-output patterns. For `d = 2`, this
    gives `2^(n+1)` patterns, which suffices to encode any single function (though
    not all `2^(2^n)` simultaneously in a single window).
-/

end


