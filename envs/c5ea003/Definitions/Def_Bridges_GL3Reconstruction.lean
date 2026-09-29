-- Prove2me | Definitions.Def_Bridges_GL3Reconstruction
-- name    : Bridges_GL3Reconstruction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:21:42.518495+00:00
-- url     : https://prove2.me/theorems/d98c7a23-c93c-43cb-9c90-73285972a4de
-- title:
--   Aether Catalog definitions — Bridges_GL3Reconstruction
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GL3Reconstruction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GL3Reconstruction.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# GL₃ Tropical Satake Finite Reconstruction

## Overview

We prove that a tropical Hecke function on the bounded dominant cone of GL₃
is uniquely determined by its restrictions to the two chamber walls (rank-2
Levi marginals) and simple-coroot edge valuations, provided these data satisfy
explicit overlap compatibility conditions. The result is packaged as a canonical
equivalence of types.

## Mathematical Content

The bounded dominant cone for GL₃ consists of integer triples `(a, b, c)` with
`B ≥ a ≥ b ≥ c ≥ 0`. The two chamber walls are:

- **α₂-wall** `W₂₃ = {(a, b, b) : a ≥ b ≥ 0}`: the last two coordinates coincide
- **α₁-wall** `W₁₂ = {(a, a, c) : a ≥ c ≥ 0}`: the first two coordinates coincide
- **Diagonal** `Δ = {(n, n, n) : n ≥ 0}`: intersection of the two walls

A **tropical Hecke function** satisfies the additive wall decomposition:
```
  f(a, b, c) = f(a, b, b) + f(b, b, c) − f(b, b, b)
```
This is the tropicalized version of the factorization of spherical functions
through rank-2 Levi subgroups, expressing that interior values decompose
additively into the two wall contributions with a diagonal correction.

The **Levi marginals** are the wall restrictions:
- `levi23Marginal f (a, b) = f(a, b, b)` on the α₂-wall
- `levi12Marginal f (a, c) = f(a, a, c)` on the α₁-wall

The **simple-coroot edge valuations** are:
- `simpleCorootEdgeVal01 f (n) = f(n, 0, 0)` along the ω₁-ray
- `simpleCorootEdgeVal12 f (n) = f(n, n, 0)` along the ω₂-ray

## Main Results

* `boundaryLeviEquiv` — Canonical `Equiv` between `TropicalHeckeFnGL3 B` and
  `CompatibleEdgeLeviData B`.
* `boundaryLeviMap_bijective` — The boundary extraction map is bijective.
* `gl3_reconstruction_unique` — Every compatible dataset has a unique preimage (`∃!`).
* `gl3_tropical_satake_bounded_reconstruction` — The full reconstruction equivalence
  with explicit component formulas.

## References

This is a concrete finite version of the tropical Satake correspondence for GL₃,
building on the injectivity results in `GL3TropicalSatake` and the surjectivity
results in `TropicalSatakeSurjectivity`.
-/

set_option maxHeartbeats 400000

namespace GL3TropRecon

/-! ## Section 1: Core Types -/

/-- Dominant coweight for GL₃ bounded by `B`: a triple `(a, b, c) ∈ ℕ³` with `B ≥ a ≥ b ≥ c`.

These parametrize dominant weights/coweights of GL₃ in the bounded region,
corresponding to isomorphism classes of irreducible representations whose
highest weight has all parts at most `B`. -/
@[ext]
structure DomWt (B : ℕ) where
  a : ℕ
  b : ℕ
  c : ℕ
  hab : b ≤ a
  hbc : c ≤ b
  haB : a ≤ B

/-- Dominant pair bounded by `B`: `(x, y) ∈ ℕ²` with `B ≥ x ≥ y`.
Used for wall/Levi data — each wall of the GL₃ dominant cone is
parametrized by such pairs. -/
@[ext]
structure DomPr (B : ℕ) where
  x : ℕ
  y : ℕ
  hle : y ≤ x
  hB : x ≤ B

/-! ## Section 2: Fintype Instances -/

/-- The bounded dominant cone is finite: embed into `Fin (B+1)³`. -/
noncomputable instance domWtFintype (B : ℕ) : Fintype (DomWt B) :=
  Fintype.ofInjective
    (fun w : DomWt B =>
      ((⟨w.a, Nat.lt_succ_of_le w.haB⟩ : Fin (B+1)),
       (⟨w.b, Nat.lt_succ_of_le (le_trans w.hab w.haB)⟩ : Fin (B+1)),
       (⟨w.c, Nat.lt_succ_of_le (le_trans w.hbc (le_trans w.hab w.haB))⟩ : Fin (B+1))))
    (fun w1 w2 h => by
      simp [Prod.mk.injEq, Fin.ext_iff] at h
      exact DomWt.ext h.1 h.2.1 h.2.2)

/-- The bounded dominant pair type is finite. -/
noncomputable instance domPrFintype (B : ℕ) : Fintype (DomPr B) :=
  Fintype.ofInjective
    (fun p : DomPr B =>
      ((⟨p.x, Nat.lt_succ_of_le p.hB⟩ : Fin (B+1)),
       (⟨p.y, Nat.lt_succ_of_le (le_trans p.hle p.hB)⟩ : Fin (B+1))))
    (fun p1 p2 h => by
      simp [Prod.mk.injEq, Fin.ext_iff] at h
      exact DomPr.ext h.1 h.2)

/-! ## Section 3: Tropical Hecke Condition -/

/-- A function `f` on bounded dominant GL₃ coweights satisfies the **tropical Hecke
additive wall decomposition** if:
```
  f(a, b, c) = f(a, b, b) + f(b, b, c) − f(b, b, b)
```
for every dominant triple `(a, b, c)` with `a ≤ B`.

This condition asserts that interior values of the dominant cone are determined
by the values on the two chamber walls via a simple additive formula with a
diagonal correction term. On the walls themselves (where `a = b` or `b = c`),
the condition is automatically satisfied. -/
def IsTropHecke (B : ℕ) (f : DomWt B → ℤ) : Prop :=
  ∀ w : DomWt B,
    f w = f ⟨w.a, w.b, w.b, w.hab, le_refl _, w.haB⟩ +
          f ⟨w.b, w.b, w.c, le_refl _, w.hbc, le_trans w.hab w.haB⟩ -
          f ⟨w.b, w.b, w.b, le_refl _, le_refl _, le_trans w.hab w.haB⟩

/-- The subtype of tropical Hecke functions on the bounded GL₃ dominant cone.
This is a genuinely finite-dimensional space when `B` is fixed. -/
def TropicalHeckeFnGL3 (B : ℕ) := { f : DomWt B → ℤ // IsTropHecke B f }

/-! ## Section 4: Compatible Boundary Data -/

/-- Compatible edge-Levi data for GL₃ bounded by `B`.

This packages the restrictions of a tropical Hecke function to the two chamber walls
of the GL₃ dominant cone, subject to the constraint that they agree on the diagonal
ray where all three coordinates coincide.

The **Levi-23 marginal** `levi23(a, b) = f(a, b, b)` gives the restriction to the
α₂-wall (where the 2nd and 3rd coordinates agree).

The **Levi-12 marginal** `levi12(a, c) = f(a, a, c)` gives the restriction to the
α₁-wall (where the 1st and 2nd coordinates agree).

The **diagonal compatibility** condition says these walls agree on the ray
`{(n, n, n) : 0 ≤ n ≤ B}`, which is their geometric intersection. -/
structure CompatibleEdgeLeviData (B : ℕ) where
  /-- The Levi-23 marginal: `f(a, b, b)` on the α₂-wall. -/
  levi23 : DomPr B → ℤ
  /-- The Levi-12 marginal: `f(a, a, c)` on the α₁-wall. -/
  levi12 : DomPr B → ℤ
  /-- Diagonal overlap compatibility: the walls agree on `{(n, n, n)}`. -/
  diagCompat : ∀ n (hn : n ≤ B),
    levi23 ⟨n, n, le_refl _, hn⟩ = levi12 ⟨n, n, le_refl _, hn⟩


/-! ## Section 5: Edge Valuations and Levi Marginals -/

/-- Extract the simple-coroot edge valuation along the ω₁-ray: `f(n, 0, 0)`. -/
def simpleCorootEdgeVal01 {B : ℕ} (f : TropicalHeckeFnGL3 B) (n : ℕ) (hn : n ≤ B) : ℤ :=
  f.1 ⟨n, 0, 0, Nat.zero_le _, Nat.zero_le _, hn⟩

/-- Extract the simple-coroot edge valuation along the ω₂-ray: `f(n, n, 0)`. -/
def simpleCorootEdgeVal12 {B : ℕ} (f : TropicalHeckeFnGL3 B) (n : ℕ) (hn : n ≤ B) : ℤ :=
  f.1 ⟨n, n, 0, le_refl _, Nat.zero_le _, hn⟩

/-- Extract the Levi-12 marginal: `f(a, a, c)` restricted to the α₁-wall. -/
def levi12Marginal {B : ℕ} (f : TropicalHeckeFnGL3 B) (p : DomPr B) : ℤ :=
  f.1 ⟨p.x, p.x, p.y, le_refl _, p.hle, p.hB⟩

/-- Extract the Levi-23 marginal: `f(a, b, b)` restricted to the α₂-wall. -/
def levi23Marginal {B : ℕ} (f : TropicalHeckeFnGL3 B) (p : DomPr B) : ℤ :=
  f.1 ⟨p.x, p.y, p.y, p.hle, le_refl _, p.hB⟩

/-! ## Section 6: Forward Map — Extract Boundary Data -/

/-- The boundary-Levi map extracts compatible wall data from a tropical Hecke function.
This is the forward direction of the reconstruction equivalence. -/
def boundaryLeviMap (B : ℕ) (f : TropicalHeckeFnGL3 B) : CompatibleEdgeLeviData B where
  levi23 p := levi23Marginal f p
  levi12 p := levi12Marginal f p
  diagCompat n hn := by
    simp only [levi23Marginal, levi12Marginal]

/-! ## Section 7: Inverse Map — Reconstruct from Boundary Data -/

/-- The reconstruction formula: given compatible wall data `d`, recover the function value
at any dominant weight `(a, b, c)` via:
```
  f(a, b, c) = d.levi23(a, b) + d.levi12(b, c) − d.levi12(b, b)
```
This is the inverse of `boundaryLeviMap`. -/
def reconstructVal (B : ℕ) (d : CompatibleEdgeLeviData B) (w : DomWt B) : ℤ :=
  d.levi23 ⟨w.a, w.b, w.hab, w.haB⟩ +
  d.levi12 ⟨w.b, w.c, w.hbc, le_trans w.hab w.haB⟩ -
  d.levi12 ⟨w.b, w.b, le_refl _, le_trans w.hab w.haB⟩

/-
The reconstructed function satisfies the tropical Hecke condition.
-/
theorem reconstructVal_isTropHecke (B : ℕ) (d : CompatibleEdgeLeviData B) :
    IsTropHecke B (reconstructVal B d) := by
  intro w;
  simp [reconstructVal];
  ring

/-- Reconstruct a tropical Hecke function from compatible boundary data. -/
def reconstructFn (B : ℕ) (d : CompatibleEdgeLeviData B) : TropicalHeckeFnGL3 B :=
  ⟨reconstructVal B d, reconstructVal_isTropHecke B d⟩

/-! ## Section 8: Roundtrip Proofs -/

/-
Right inverse: extracting boundary data from a reconstruction recovers
the original compatible data. Uses the diagonal compatibility condition.
-/
theorem roundtrip_right (B : ℕ) (d : CompatibleEdgeLeviData B) :
    boundaryLeviMap B (reconstructFn B d) = d := by
  unfold boundaryLeviMap reconstructFn levi12Marginal;
  unfold reconstructVal levi23Marginal;
  simp +decide [ d.diagCompat ]

/-
Left inverse: reconstructing from extracted boundary data recovers
the original tropical Hecke function. Uses the Hecke decomposition condition.
-/
theorem roundtrip_left (B : ℕ) (f : TropicalHeckeFnGL3 B) :
    reconstructFn B (boundaryLeviMap B f) = f := by
  -- By definition of `reconstructFn`, we have `reconstructFn B (boundaryLeviMap B f) = ⟨reconstructVal B (boundaryLeviMap B f), reconstructVal_isTropHecke B (boundaryLeviMap B f)⟩`.
  apply Subtype.ext;
  ext w;
  exact f.2 w ▸ rfl

/-! ## Section 9: The Canonical Equivalence -/

/-- The canonical equivalence between tropical Hecke functions on bounded
GL₃ dominant coweights and compatible edge-Levi boundary data.

This is the **tropical Satake finite reconstruction**: every bounded-support
tropical Hecke function for GL₃ is uniquely encoded by its rank-2 Levi
marginals (wall restrictions) together with the diagonal compatibility
constraint, with no loss and no redundancy. -/
def boundaryLeviEquiv (B : ℕ) : TropicalHeckeFnGL3 B ≃ CompatibleEdgeLeviData B where
  toFun := boundaryLeviMap B
  invFun := reconstructFn B
  left_inv := roundtrip_left B
  right_inv := roundtrip_right B




/-! ## Section 10: Unique Reconstruction -/


/-! ## Section 11: Injectivity from Agreement on Marginals -/

/-
Two tropical Hecke functions with identical Levi marginals are equal.
This is the separation principle: the wall data separates points.
-/

/-! ## Section 12: Edge Data -/



/-! ## Section 13: Full Reconstruction Statement -/


/-! ## Section 14: Extensionality on Bounded Dominant Support -/


/-! ## Section 15: Levi Face Overlaps -/




end GL3TropRecon


