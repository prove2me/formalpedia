-- Prove2me | Definitions.Def_Algebra_SmoothWindows_GaborOperators
-- name    : Algebra_SmoothWindows_GaborOperators
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T17:00:18.865732+00:00
-- url     : https://prove2.me/theorems/1b137d22-ce1f-4127-b889-1069953c2c68
-- title:
--   Aether Catalog definitions — Algebra_SmoothWindows_GaborOperators
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.SmoothWindows.GaborOperators`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/SmoothWindows/GaborOperators.lean by skeleton subtraction
import Mathlib

/-!
# Smooth windows I: translation, modulation and the Weyl relation

The Reciprocal-Zero Harmonics programme (`Algebra.ReciprocalZeroHarmonics.Core`,
`Algebra.ReciprocalZeroHarmonics.WindowDichotomy`) analyses spectral data through the
*rectangular* window `|Im ρ| ≤ T`.  This file lays the algebraic foundation for replacing that
sharp cutoff by a smooth (Gaussian / Schwartz) window: the two families of operators that move a
window around phase space,

* **translation** `(T_a f)(t) = f (t - a)`,
* **modulation** `(M_b f)(t) = e^{2πi b t} f (t)`,

and the *modulation/translation identity* (the Weyl commutation relation) that they satisfy.

## Main results

* `modOp_transOp` — **Weyl commutation relation**: `M_b T_a = χ(b a) · T_a M_b`, where
  `χ(x) = e^{2πix}`.  Translation and modulation commute only up to the phase `e^{2πi ab}`; this
  failure of commutativity *is* the Heisenberg group.
* `Heis` — the (circle-valued) **Heisenberg group** with multiplication
  `(a,b,z)·(a',b',z') = (a+a', b+b', z z' χ(b a'))`, with a full `Group` instance proved from the
  cocycle identity.
* `heisRep` — the **Schrödinger/Gabor representation** `Heis →* Function.End (ℝ → ℂ)`,
  `(a,b,z) ↦ z · T_a M_b`: a genuine monoid homomorphism, i.e. the Weyl relation is exactly what
  makes the composite of two Gabor shifts a third one.
* `heisRep_injective` — the representation is **faithful**: the Gaussian is a test vector which
  separates all Heisenberg elements.  Consequently the phase factor in `modOp_transOp` cannot be
  removed by any renormalisation of the operators.
* `modOp_transOp_ne` — an adversarial check: the phase is really needed, the two orders of
  composition differ on any window that is nonzero at the origin.

-- !-- Lab Notes -- !--
* **Hypothesis (Hypothesizer).** Windowing should be an *action of a group*, not an ad hoc
  cutoff; the correct group is the Heisenberg group, and the rectangular window of the catalog is
  merely one (non-smooth) vector in a representation space.
* **Experiment (Experimenter).** All operator identities reduce to `Complex.exp_add` after
  clearing casts; the group axioms for `Heis` reduce to the cocycle identity
  `b·a' + (b+b')·a'' = b'·a'' + b·(a' + a'')`.  Faithfulness needed a genuinely analytic input:
  the Gaussian test vector is nowhere zero and has a unique maximum, which pins down `a`, then
  the phase `z`, then the modulation `b` via `χ(1/4) = i ≠ 1`.
* **Analysis (Analyst).** The phase cocycle `χ(ba')` is not a coboundary — faithfulness shows the
  central `Circle` factor is not redundant.  This is the structural reason a *smooth* window can
  be moved freely in phase space while keeping all of its algebraic bookkeeping exact.
* **Critique (Critic).** Nothing here is definitional: `modOp_transOp` is false without the phase
  (`modOp_transOp_ne`), and `heisRep_injective` shows the group is not a proper quotient.
-/

namespace SmoothWindows

open Complex Real

/-! ## The character `χ(x) = e^{2πix}` -/

/-- The basic additive character `χ(x) = e^{2πix}` of `ℝ`. -/
noncomputable def chi (x : ℝ) : ℂ := Complex.exp ((2 * π * x : ℝ) * Complex.I)

@[simp] theorem chi_zero : chi 0 = 1 := by simp [chi]

theorem chi_add (x y : ℝ) : chi (x + y) = chi x * chi y := by
  unfold chi
  rw [← Complex.exp_add]
  push_cast
  ring_nf

@[simp] theorem chi_ne_zero (x : ℝ) : chi x ≠ 0 := Complex.exp_ne_zero _


theorem chi_neg (x : ℝ) : chi (-x) = (chi x)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← chi_add]
  simp

/-- `χ` is the coercion of `Circle.exp (2πx)`. -/
theorem coe_circleExp (x : ℝ) : (Circle.exp (2 * π * x) : ℂ) = chi x := by
  rw [Circle.coe_exp, chi]



/-! ## Translation and modulation -/

/-- **Translation** `(T_a f)(t) = f (t - a)`. -/
def transOp (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := fun t => f (t - a)

/-- **Modulation** `(M_b f)(t) = e^{2πi b t} f (t)`. -/
noncomputable def modOp (b : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := fun t => chi (b * t) * f t










/-! ## The Heisenberg group and the Gabor representation -/

/-- The (circle-valued) **Heisenberg group**: triples `(a, b, z)` of a translation, a modulation
and a unimodular phase, multiplied through the Weyl cocycle. -/
structure Heis where
  /-- the translation parameter -/
  a : ℝ
  /-- the modulation parameter -/
  b : ℝ
  /-- the central phase -/
  z : Circle

namespace Heis

@[ext] theorem ext {g h : Heis} (ha : g.a = h.a) (hb : g.b = h.b) (hz : g.z = h.z) : g = h := by
  cases g; cases h; simp_all

noncomputable instance : One Heis := ⟨⟨0, 0, 1⟩⟩

noncomputable instance : Mul Heis :=
  ⟨fun g h => ⟨g.a + h.a, g.b + h.b, g.z * h.z * Circle.exp (2 * π * (g.b * h.a))⟩⟩

noncomputable instance : Inv Heis :=
  ⟨fun g => ⟨-g.a, -g.b, g.z⁻¹ * Circle.exp (2 * π * (g.b * g.a))⟩⟩


@[simp] theorem one_a : (1 : Heis).a = 0 := rfl
@[simp] theorem one_b : (1 : Heis).b = 0 := rfl
@[simp] theorem one_z : (1 : Heis).z = 1 := rfl
@[simp] theorem mul_a (g h : Heis) : (g * h).a = g.a + h.a := rfl
@[simp] theorem mul_b (g h : Heis) : (g * h).b = g.b + h.b := rfl
@[simp] theorem mul_z (g h : Heis) :
    (g * h).z = g.z * h.z * Circle.exp (2 * π * (g.b * h.a)) := rfl
@[simp] theorem inv_a (g : Heis) : g⁻¹.a = -g.a := rfl
@[simp] theorem inv_b (g : Heis) : g⁻¹.b = -g.b := rfl
@[simp] theorem inv_z (g : Heis) : g⁻¹.z = g.z⁻¹ * Circle.exp (2 * π * (g.b * g.a)) := rfl

/-- The Heisenberg group law: associativity is precisely the 2-cocycle identity for the Weyl
phase `2π b a'`. -/
noncomputable instance : Group Heis where
  mul_assoc g h k := by
    refine Heis.ext (by simp [add_assoc]) (by simp [add_assoc]) ?_
    have e1 : Circle.exp (2 * π * ((g.b + h.b) * k.a))
        = Circle.exp (2 * π * (h.b * k.a)) * Circle.exp (2 * π * (g.b * k.a)) := by
      rw [← Circle.exp_add]; ring_nf
    have e2 : Circle.exp (2 * π * (g.b * (h.a + k.a)))
        = Circle.exp (2 * π * (g.b * h.a)) * Circle.exp (2 * π * (g.b * k.a)) := by
      rw [← Circle.exp_add]; ring_nf
    simp only [mul_z, mul_a, mul_b, e1, e2]
    simp [mul_comm, mul_left_comm, mul_assoc]
  one_mul g := Heis.ext (by simp) (by simp) (by simp)
  mul_one g := Heis.ext (by simp) (by simp) (by simp)
  inv_mul_cancel g := by
    refine Heis.ext (by simp) (by simp) ?_
    have : Circle.exp (2 * π * (g.b * g.a)) * Circle.exp (2 * π * (-g.b * g.a)) = 1 := by
      rw [← Circle.exp_add, show 2 * π * (g.b * g.a) + 2 * π * (-g.b * g.a) = 0 by ring]
      simp
    simp only [mul_z, inv_b, inv_z, one_z]
    rw [mul_assoc, mul_mul_mul_comm, inv_mul_cancel, this, mul_one]

end Heis

/-- The **Schrödinger (Gabor) representation** of the Heisenberg group on functions `ℝ → ℂ`:
`(a, b, z) ↦ z · T_a M_b`. -/
noncomputable def gaborAct (g : Heis) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => (g.z : ℂ) * transOp g.a (modOp g.b f) t

theorem gaborAct_apply (g : Heis) (f : ℝ → ℂ) (t : ℝ) :
    gaborAct g f t = (g.z : ℂ) * chi (g.b * (t - g.a)) * f (t - g.a) := by
  simp [gaborAct, transOp, modOp, mul_assoc]

@[simp] theorem gaborAct_one (f : ℝ → ℂ) : gaborAct 1 f = f := by
  funext t; simp [gaborAct_apply]

/-- **The representation property.**  The composite of two Gabor shifts is the Gabor shift of the
Heisenberg product — this is exactly the modulation/translation identity in group form. -/
theorem gaborAct_mul (g h : Heis) (f : ℝ → ℂ) :
    gaborAct (g * h) f = gaborAct g (gaborAct h f) := by
  funext t
  simp only [gaborAct_apply, Heis.mul_a, Heis.mul_b, Heis.mul_z, Circle.coe_mul, coe_circleExp]
  rw [show t - (g.a + h.a) = (t - g.a) - h.a by ring,
    show chi ((g.b + h.b) * (t - g.a - h.a))
      = chi (g.b * (t - g.a)) * chi (h.b * ((t - g.a) - h.a)) * (chi (g.b * h.a))⁻¹ by
      rw [← chi_add, ← chi_neg, ← chi_add]; congr 1; ring]
  field_simp

/-- The Gabor representation packaged as a monoid homomorphism into the endomorphism monoid of
the space of windows. -/
noncomputable def heisRep : Heis →* Function.End (ℝ → ℂ) where
  toFun g := gaborAct g
  map_one' := by funext f; exact gaborAct_one f
  map_mul' g h := by funext f; exact gaborAct_mul g h f


/-- The Gaussian test window used to prove faithfulness. -/
noncomputable def gaussTest : ℝ → ℂ := fun t => ((Real.exp (-t ^ 2) : ℝ) : ℂ)




end SmoothWindows


