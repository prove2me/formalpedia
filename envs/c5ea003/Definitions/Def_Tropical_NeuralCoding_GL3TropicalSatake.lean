-- Prove2me | Definitions.Def_Tropical_NeuralCoding_GL3TropicalSatake
-- name    : Tropical_NeuralCoding_GL3TropicalSatake
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:02.99021+00:00
-- url     : https://prove2.me/theorems/7a01e0dc-301f-4181-b284-743c76391517
-- title:
--   Aether Catalog definitions — Tropical_NeuralCoding_GL3TropicalSatake
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.NeuralCoding.GL3TropicalSatake`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/NeuralCoding/GL3TropicalSatake.lean by skeleton subtraction
import Mathlib
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

namespace GL3TropSatake

/-! ## Section 1: Basic Types -/

/-- Dominant coweights for GL₃: integer triples (a, b, c) with a ≥ b ≥ c.
These parametrize dominant weights of the dual torus, or equivalently,
isomorphism classes of irreducible representations of GL₃. -/
def DomGL3 := {x : ℤ × ℤ × ℤ // x.1 ≥ x.2.1 ∧ x.2.1 ≥ x.2.2}

/-- Tropical values: ℤ ∪ {-∞}, the value monoid of the max-plus semiring. -/
abbrev Trop := WithBot ℤ

/-- Tropical functions on the GL₃ dominant chamber. -/
abbrev TropFn := DomGL3 → Trop

/-! ## Section 2: Arithmetic on Integer Triples -/

/-- Componentwise addition of integer triples. -/
def addTriple (a b : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

/-- Componentwise subtraction of integer triples. -/
def subTriple (a b : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (a.1 - b.1, a.2.1 - b.2.1, a.2.2 - b.2.2)

/-- Dominance predicate: a triple is dominant if its components are weakly decreasing. -/
def isDom (x : ℤ × ℤ × ℤ) : Prop := x.1 ≥ x.2.1 ∧ x.2.1 ≥ x.2.2

instance isDom_decidable (x : ℤ × ℤ × ℤ) : Decidable (isDom x) := by
  unfold isDom; exact inferInstance


/-- The sum of two dominant weights is dominant. This is the fundamental
algebraic property of the dominant cone: it is a sub-semigroup of (ℤ³, +). -/
lemma addTriple_dom (a b : ℤ × ℤ × ℤ) (ha : isDom a) (hb : isDom b) :
    isDom (addTriple a b) := by
  simp only [isDom, addTriple] at *; constructor <;> omega

/-! ## Section 3: Dominant Weight Arithmetic -/

/-- Addition of dominant weights. The sum of two dominant weights is dominant
because the dominant cone is closed under addition. -/
def domAdd (mu alpha : DomGL3) : DomGL3 :=
  ⟨addTriple mu.val alpha.val, addTriple_dom mu.val alpha.val mu.prop alpha.prop⟩


/-! ## Section 4: Fundamental Coweights -/

/-- The first fundamental coweight ω₁ = (1, 0, 0).
Corresponds to the standard representation of GL₃. -/
def omega1 : DomGL3 := ⟨(1, 0, 0), by decide⟩

/-- The second fundamental coweight ω₂ = (1, 1, 0).
Corresponds to the exterior square ∧²(standard) of GL₃. -/
def omega2 : DomGL3 := ⟨(1, 1, 0), by decide⟩

/-- The third fundamental coweight ω₃ = (1, 1, 1).
Corresponds to the determinant representation of GL₃. -/
def omega3 : DomGL3 := ⟨(1, 1, 1), by decide⟩

/-! ## Section 5: Tropical Convolution with Delta Functions -/

/-- Tropical convolution of f with the delta function δ_α.
Defined as (f ⊛ δ_α)(wt) = f(wt - α) when wt - α is dominant, ⊥ otherwise.

This is the tropicalization of the Hecke algebra action: in the classical
(p-adic) setting, convolution with the characteristic function of
K·diag(π^α)·K acts on the space of K-bi-invariant functions. In the
tropical limit, this becomes a shift operation on the dominant chamber. -/
noncomputable def tconvDelta (f : TropFn) (alpha : DomGL3) (wt : DomGL3) : Trop :=
  if h : isDom (subTriple wt.val alpha.val) then
    f ⟨subTriple wt.val alpha.val, h⟩
  else ⊥


/-! ## Section 6: Core Injectivity Theorem -/


/-! ## Section 7: Test Function Predicates -/

/-- A rank-1 Levi test for simple root i tests in the direction of the i-th
fundamental weight. Concretely, the test function has a positive gap in the
i-th simple root direction. -/
def IsRankOneLeviTest (i : Fin 2) (alpha : DomGL3) : Prop :=
  match i with
  | 0 => alpha.val.1 > alpha.val.2.1  -- positive first gap
  | 1 => alpha.val.2.1 > alpha.val.2.2  -- positive second gap

/-- A central (determinant) test function has equal components:
it shifts uniformly in all coordinate directions. -/
def IsCentralOrDetTest (alpha : DomGL3) : Prop :=
  alpha.val.1 = alpha.val.2.1 ∧ alpha.val.2.1 = alpha.val.2.2

/-- The test family generates adjacent facet valuations: together, the three
test functions span all directions of the dominant chamber. -/
def GeneratesAdjacentFacetValuations (t1 t2 t3 : DomGL3) : Prop :=
  IsRankOneLeviTest 0 t1 ∧ IsRankOneLeviTest 1 t2 ∧ IsCentralOrDetTest t3





/-! ## Section 8: Main Injectivity Theorems -/




/-! ## Section 9: Facet Valuations

We define the three facet valuation operators and prove they are determined
by the test function convolutions. -/

/-- The first facet valuation: evaluates f at the shift μ + ω₁. -/
noncomputable def facetVal1 (f : TropFn) (mu : DomGL3) : Trop :=
  tconvDelta f omega1 (domAdd mu omega1)

/-- The second facet valuation: evaluates f at the shift μ + ω₂. -/
noncomputable def facetVal2 (f : TropFn) (mu : DomGL3) : Trop :=
  tconvDelta f omega2 (domAdd mu omega2)

/-- The central valuation: evaluates f at the shift μ + ω₃. -/
noncomputable def centralVal (f : TropFn) (mu : DomGL3) : Trop :=
  tconvDelta f omega3 (domAdd mu omega3)





/-! ## Section 10: Weyl-Symmetrized Convolution

For the Weyl group W = S₃ of GL₃, the **Weyl-symmetrized** tropical convolution
is more natural from the representation-theoretic perspective. Here, δ_{ω₁}
contributes from all permutations of its weight, giving:

  (f ⊛_W δ_{ω₁})(wt) = max(f(sort(wt - e₁)), f(sort(wt - e₂)), f(sort(wt - e₃)))

where e₁, e₂, e₃ are the standard basis vectors and sort arranges components
in decreasing order. -/

/-- Sort a triple of integers into weakly decreasing order (dominant representative). -/
def sortTriple (x : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  let a := max x.1 (max x.2.1 x.2.2)
  let c := min x.1 (min x.2.1 x.2.2)
  let b := x.1 + x.2.1 + x.2.2 - a - c
  (a, b, c)

/-- The sorted triple is always dominant. -/
lemma sortTriple_isDom (x : ℤ × ℤ × ℤ) : isDom (sortTriple x) := by
  simp only [isDom, sortTriple]; constructor <;> omega

/-- Convert any integer triple to a dominant weight by sorting. -/
def toDom (x : ℤ × ℤ × ℤ) : DomGL3 := ⟨sortTriple x, sortTriple_isDom x⟩


/-- Weyl-symmetrized tropical convolution with δ_{ω₁}.
Takes the max of f applied to the sorted versions of wt minus each
standard basis vector. -/
noncomputable def weylConv1 (f : TropFn) (wt : DomGL3) : Trop :=
  let a := wt.val.1; let b := wt.val.2.1; let c := wt.val.2.2
  max (f (toDom (a - 1, b, c)))
      (max (f (toDom (a, b - 1, c))) (f (toDom (a, b, c - 1))))

/-- Weyl-symmetrized tropical convolution with δ_{ω₂}.
Takes the max over the three ways to subtract two distinct basis vectors. -/
noncomputable def weylConv2 (f : TropFn) (wt : DomGL3) : Trop :=
  let a := wt.val.1; let b := wt.val.2.1; let c := wt.val.2.2
  max (f (toDom (a - 1, b - 1, c)))
    (max (f (toDom (a - 1, b, c - 1))) (f (toDom (a, b - 1, c - 1))))

/-- Weyl-symmetrized tropical convolution with δ_{ω₃}.
Since all permutations of (1,1,1) are (1,1,1), this is just a shift. -/
noncomputable def weylConv3 (f : TropFn) (wt : DomGL3) : Trop :=
  f (toDom (wt.val.1 - 1, wt.val.2.1 - 1, wt.val.2.2 - 1))


/-! ## Section 11: The Operator Packaging -/

/-- The test family operator: maps a tropical function to its triple of convolutions. -/
noncomputable def testFamilyOperator (f : TropFn) : TropFn × TropFn × TropFn :=
  (tconvDelta f omega1, tconvDelta f omega2, tconvDelta f omega3)


/-- The Weyl test family operator. -/
noncomputable def weylTestFamilyOperator (f : TropFn) : TropFn × TropFn × TropFn :=
  (weylConv1 f, weylConv2 f, weylConv3 f)


/-! ## Section 12: Generalization to GLₙ

The key algebraic fact — that the dominant cone is closed under addition —
holds for any root system. We state this as an abstract shift injectivity result. -/


end GL3TropSatake


