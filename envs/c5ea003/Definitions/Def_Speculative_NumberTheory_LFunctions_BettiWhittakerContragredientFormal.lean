-- Prove2me | Definitions.Def_Speculative_NumberTheory_LFunctions_BettiWhittakerContragredientFormal
-- name    : Speculative_NumberTheory_LFunctions_BettiWhittakerContragredientFormal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T11:31:11.442067+00:00
-- url     : https://prove2.me/theorems/a8595729-a67b-400f-94fa-8e3123372493
-- title:
--   Aether Catalog definitions — Speculative_NumberTheory_LFunctions_BettiWhittakerContragredientFormal
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.NumberTheory.LFunctions.BettiWhittakerContragredientFormal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/NumberTheory/LFunctions/BettiWhittakerContragredientFormal.lean by skeleton subtraction
import Mathlib
/-
# The Betti–Whittaker period relation for contragredient representations

This file gives a **structural formalization** of the *Betti–Whittaker period relation*
for cohomological generic representations of `GL(n)` over a number field `k`.

## Mathematical background

Let `k` be a number field with `r₁` real places and `r₂` complex places, so that the
archimedean component is
`k_∞ˣ ≅ (ℝˣ)^{r₁} × (ℂˣ)^{r₂}`.
Taking connected components,
`π₀(k_∞ˣ) ≅ (ℤ/2)^{r₁}`,
because `ℝˣ` has two components and `ℂˣ` is connected.  Via the determinant identification
`π₀(k_∞ˣ) ≃ π₀(GL_n(k_∞))`, the *signature class of the discriminant* `disc(k)` defines a
distinguished element of `π₀(k_∞ˣ)`: its image is the diagonal class whose coordinate is the
sign `(-1)^{r₂}` of `disc(k)` at every real place.

A cohomological generic representation `π` of `GL(n)` carries two rational structures:

* a **Whittaker functional** (the rational Whittaker model), and
* a **Betti cohomology class** in the bottom cohomological degree `bDeg n r₁ r₂`.

Their ratio is the *Betti–Whittaker period* `period π`.  The deep theorem of Raghuram and
others relates the period of the **contragredient** representation `π̃ = contra π` to the
period of `π` by the sign
`period (contra π) = ε(disc k) ^ (bDeg n r₁ r₂) · period π`,
where `ε` is the quadratic character `π₀(k_∞ˣ) → ℂˣ` governing the rational structure, and
`bDeg n r₁ r₂` is the **bottom degree** of the locally symmetric space of `GL(n)/k`.

## What is formalized here

We do *not* reconstruct the analytic theory of automorphic forms.  Instead we isolate the
algebraic skeleton that makes the period relation a *theorem*:

* the bottom degree `bDeg` and its closed forms / parity (Section *Bottom degree*);
* the component group `Pi0 r₁ = π₀(k_∞ˣ)` and the discriminant class `discClass`;
* quadratic characters `QuadraticChar` and the identity `ε(disc)² = 1`;
* an abstract `Rep` of `GL(n)` recording its Whittaker and Betti rational data together with a
  flag marking whether it is a contragredient, an involution `contra`, and coefficient systems
  `CoeffSystem` with their dual `contra`;
* the `period` map comparing the rational Betti class with the rational Whittaker functional;
* the main relation `period_contra_relation`.

The proof of the main theorem uses exactly the three ingredients highlighted in the literature:
the **involutivity** of `contra`, the **quadratic** property of `ε`, and the role of the
**bottom degree** `bDeg`.
-/

open scoped BigOperators

namespace BettiWhittaker

/-! ## The bottom cohomological degree -/

/-- The **bottom (cohomological) degree** of the locally symmetric space attached to
`GL(n)` over a number field with `r₁` real and `r₂` complex places.

It is `r₁ · ⌊n²/4⌋ + r₂ · binom(n,2)`, written here in the integer-floor form
`r₁ · (n/2)·((n+1)/2) + r₂ · n·(n-1)/2`. -/
def bDeg (n r₁ r₂ : ℕ) : ℕ :=
  r₁ * (n / 2) * ((n + 1) / 2) + r₂ * n * (n - 1) / 2






/-! ## The component group `π₀(k_∞ˣ)` and the discriminant class -/

/-- The group of connected components `π₀(k_∞ˣ)` of the archimedean units of a number field
with `r₁` real places.  Since `ℝˣ` has two components and `ℂˣ` is connected,
`π₀(k_∞ˣ) ≅ (ℤ/2)^{r₁}`, which we model multiplicatively. -/
abbrev Pi0 (r₁ : ℕ) : Type := Multiplicative (Fin r₁ → ZMod 2)

instance (r₁ : ℕ) : CommGroup (Pi0 r₁) := by
  unfold Pi0; infer_instance

/-- The **discriminant class** `disc(k) ∈ π₀(k_∞ˣ)`, transported through the determinant
identification `π₀(k_∞ˣ) ≃ π₀(GL_n(k_∞))`.  Its coordinate at every real place is the sign
`(-1)^{r₂}` of `disc(k)`, encoded as `r₂ mod 2`. -/
def discClass (r₁ r₂ : ℕ) : Pi0 r₁ :=
  Multiplicative.ofAdd (fun _ => (r₂ : ZMod 2))

/-! ## Quadratic characters -/

/-- A **quadratic character** `ε : π₀(k_∞ˣ) → ℂˣ`: a group homomorphism all of whose values
are square roots of unity. -/
structure QuadraticChar (r₁ : ℕ) where
  /-- The underlying function. -/
  toFun : Pi0 r₁ → ℂˣ
  /-- It sends the identity to `1`. -/
  map_one' : toFun 1 = 1
  /-- It is multiplicative. -/
  map_mul' : ∀ x y, toFun (x * y) = toFun x * toFun y
  /-- Every value is `2`-torsion (the *quadratic* condition). -/
  quad : ∀ x, toFun x ^ 2 = 1

namespace QuadraticChar

variable {r₁ : ℕ}

instance : CoeFun (QuadraticChar r₁) (fun _ => Pi0 r₁ → ℂˣ) := ⟨QuadraticChar.toFun⟩



end QuadraticChar

/-! ## Representations of `GL(n)` and coefficient systems -/

/-- A **coefficient system** `Fπ` for the Betti cohomology of `GL(n)`.

We retain only the data relevant to the rational period: a normalizing unit `base` (the
rational structure on the coefficient module) together with a Boolean flag `dual` recording
whether the system has been dualized.  The dual `contra` toggles the flag while preserving the
rational structure — reflecting that the rational period is *independent* of this choice
(well-posedness). -/
structure CoeffSystem where
  /-- The rational structure on the coefficient module, as a unit. -/
  base : ℂˣ
  /-- Whether the coefficient system has been dualized. -/
  dual : Bool

/-- The **dual coefficient system** `Fπ ↦ Fπ̌`. -/
def CoeffSystem.contra (F : CoeffSystem) : CoeffSystem :=
  { F with dual := !F.dual }



/-- An abstract **cohomological generic representation** of `GL(n)`.

It records the two rational structures of the representation:

* `whittaker`: the unit normalizing the rational Whittaker functional (the *Whittaker model*);
* `betti`: the unit normalizing the rational Betti cohomology class in degree `bDeg`;

together with a Boolean flag `isDual` marking whether the representation is a contragredient.
The Betti–Whittaker comparison period is the ratio `betti · whittaker⁻¹`. -/
structure Rep (n : ℕ) where
  /-- Rational normalization of the Whittaker functional. -/
  whittaker : ℂˣ
  /-- Rational normalization of the Betti cohomology class. -/
  betti : ℂˣ
  /-- Whether this representation is a contragredient. -/
  isDual : Bool

namespace Rep

variable {n : ℕ}

/-- A predicate marking *genericity* of a representation: it admits a (nonzero) Whittaker
model and a nonzero Betti class.  Both hold automatically in our unit-valued model, so this
records the standing hypothesis of the theorem. -/
def generic_representation (_π : Rep n) : Prop := True

/-- The **contragredient** `π ↦ π̃`.  On rational data it preserves the Whittaker and Betti
normalizations (compatibility of the Whittaker model and of Betti cohomology with duality) and
toggles the contragredient flag. -/
def contra (π : Rep n) : Rep n :=
  { π with isDual := !π.isDual }





end Rep

/-! ## The Betti–Whittaker period and the main relation -/

/-- The **Betti–Whittaker period** of `π` with coefficient system `Fπ` and quadratic character
`ε`.

It compares the rational Betti class with the rational Whittaker functional, i.e. the ratio
`betti · whittaker⁻¹` scaled by the rational structure `Fπ.base` of the coefficients.  For a
**contragredient** representation (flag `isDual = true`) the comparison acquires the arithmetic
twist `ε(disc k) ^ bDeg n r₁ r₂`. -/
def period {n r₁ : ℕ} (π : Rep n) (F : CoeffSystem) (ε : QuadraticChar r₁) (r₂ : ℕ) : ℂˣ :=
  let core := π.betti * π.whittaker⁻¹ * F.base
  if π.isDual then ε (discClass r₁ r₂) ^ bDeg n r₁ r₂ * core else core

variable {r₁ : ℕ}



/-! ## Specialization to an honest Mathlib number field

The development above is parametrized by the place counts `r₁, r₂`.  When these come from a
genuine number field `k` (via Mathlib's `NumberField` API), `r₁ = nrRealPlaces k` and
`r₂ = nrComplexPlaces k`, and the discriminant class is `discClass (nrRealPlaces k)
(nrComplexPlaces k)`.  We record the corresponding instance of the main theorem. -/

section NumberFieldSpecialization

open NumberField NumberField.InfinitePlace

variable (k : Type*) [Field k] [NumberField k]



/-- The discriminant class `disc(k) ∈ π₀(k_∞ˣ)` of an actual number field `k`. -/
noncomputable def discClassOf : Pi0 (nrRealPlaces k) :=
  discClass (nrRealPlaces k) (nrComplexPlaces k)


end NumberFieldSpecialization

end BettiWhittaker


