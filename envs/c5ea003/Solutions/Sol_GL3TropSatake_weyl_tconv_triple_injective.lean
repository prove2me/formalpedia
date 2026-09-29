-- Prove2me | solution 1 for GL3TropSatake.weyl_tconv_triple_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:58:08.584157+00:00
-- url     : https://prove2.me/submissions/9f6305c0-ff37-415a-b20b-da8cae6ec0de

-- Sol generated from Tropical/NeuralCoding/GL3TropicalSatake.lean
import Mathlib
import Definitions.Def_Tropical_NeuralCoding_GL3TropicalSatake
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# GL₃ Tropical Satake Uniqueness

## Main Results

We prove that a tropical function on the GL₃ dominant chamber is uniquely
determined by its tropical convolutions with rank-1 Levi test functions.

### Core Theorems

* `tconvDelta_injective` — Convolution with *any* dominant delta function is injective.
  This is the key algebraic fact: the dominant cone is closed under addition,
  so shifting by any dominant vector is a bijection on the dominant chamber.

* `gl3_tropical_satake_testFamily_injective` — The three-test-function operator
  `f ↦ (f ⊛ δ_{ω₁}, f ⊛ δ_{ω₂}, f ⊛ δ_{ω₃})` is injective, where ω₁, ω₂, ω₃
  are the fundamental coweights (1,0,0), (1,1,0), (1,1,1).

* `gl3_tropical_satake_testFamily_unique` — Extensional uniqueness: if two tropical
  functions agree on all three convolutions, they are equal.

* `weyl_tconv_triple_injective` — For the Weyl-symmetrized convolution (which takes
  max over S₃-orbits), the three fundamental coweight tests together still determine f.

### Mathematical Context

The tropical Satake correspondence identifies finitely-supported tropical functions on
dominant coweights with elements of the tropical spherical Hecke algebra. The injectivity
theorems here establish that the "evaluation at three generators" map is faithful — this
is the **operator separation principle** for the GL₃ tropical Hecke algebra.

The three test functions correspond to the three fundamental representations of GL₃:
- ω₁ = (1,0,0): the standard representation
- ω₂ = (1,1,0): the exterior square ∧²
- ω₃ = (1,1,1): the determinant representation
-/

open GL3TropSatake

/-! ## Section 1: Basic Types -/




/-! ## Section 2: Arithmetic on Integer Triples -/







/-! ## Section 3: Dominant Weight Arithmetic -/



/-! ## Section 4: Fundamental Coweights -/




/-! ## Section 5: Tropical Convolution with Delta Functions -/



/-! ## Section 6: Core Injectivity Theorem -/


/-! ## Section 7: Test Function Predicates -/

 -- positive second gap







/-! ## Section 8: Main Injectivity Theorems -/




/-! ## Section 9: Facet Valuations

We define the three facet valuation operators and prove they are determined
by the test function convolutions. -/








/-! ## Section 10: Weyl-Symmetrized Convolution

For the Weyl group W = S₃ of GL₃, the **Weyl-symmetrized** tropical convolution
is more natural from the representation-theoretic perspective. Here, δ_{ω₁}
contributes from all permutations of its weight, giving:

  (f ⊛_W δ_{ω₁})(wt) = max(f(sort(wt - e₁)), f(sort(wt - e₂)), f(sort(wt - e₃)))

where e₁, e₂, e₃ are the standard basis vectors and sort arranges components
in decreasing order. -/




/-- Sorting a dominant triple is the identity. -/
lemma sortTriple_of_isDom (x : ℤ × ℤ × ℤ) (hx : isDom x) :
    sortTriple x = x := by
  simp only [sortTriple, isDom] at *
  obtain ⟨h1, h2⟩ := hx
  ext <;> simp <;> omega





/-! ## Section 11: The Operator Packaging -/





/-! ## Section 12: Generalization to GLₙ

The key algebraic fact — that the dominant cone is closed under addition —
holds for any root system. We state this as an abstract shift injectivity result. -/



open GL3TropSatake in
theorem solution:
    Function.Injective (fun f : TropFn => (weylConv1 f, weylConv2 f, weylConv3 f)) := by
  intro f g h
  have h3 : weylConv3 f = weylConv3 g := by
    have := h; simp [Prod.mk.injEq] at this; exact this.2.2
  funext mu
  -- Use weylConv3 to recover f and g at mu
  -- weylConv3 f wt = f(toDom(wt.1 - 1, wt.2.1 - 1, wt.2.2 - 1))
  -- Choose wt = mu + omega3 = (mu.1 + 1, mu.2.1 + 1, mu.2.2 + 1)
  let wt : DomGL3 := domAdd mu omega3
  have key := congr_fun h3 wt
  simp only [weylConv3] at key
  have sort_eq : toDom (wt.val.1 - 1, wt.val.2.1 - 1, wt.val.2.2 - 1) = mu := by
    apply Subtype.ext
    simp [wt, domAdd, addTriple, omega3, toDom]
    exact sortTriple_of_isDom mu.val mu.prop
  rw [sort_eq] at key
  exact key
