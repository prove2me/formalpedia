-- Prove2me | solution 1 for SmoothWindows.heisRep_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T21:27:58.723396+00:00
-- url     : https://prove2.me/submissions/7e15d610-1a2f-4afb-95d3-2fc49188ae66

-- Sol generated from Algebra/SmoothWindows/GaborOperators.lean
import Mathlib
import Definitions.Def_Algebra_SmoothWindows_GaborOperators
import Theorems.Thm_SmoothWindows_chi_eq_one_iff
import Theorems.Thm_SmoothWindows_norm_chi

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

open SmoothWindows

open Complex Real

/-! ## The character `χ(x) = e^{2πix}` -/









theorem chi_quarter_ne_one : chi (1 / 4 : ℝ) ≠ 1 := by
  intro hchi
  rw [chi_eq_one_iff] at hchi
  obtain ⟨n, hn⟩ := hchi
  have h4 : (4 : ℝ) * (n : ℝ) = 1 := by rw [← hn]; norm_num
  have : (4 : ℤ) * n = 1 := by exact_mod_cast h4
  omega

/-! ## Translation and modulation -/












/-! ## The Heisenberg group and the Gabor representation -/


open Heis


noncomputable instance : One Heis := ⟨⟨0, 0, 1⟩⟩













theorem gaussTest_ne_zero (t : ℝ) : gaussTest t ≠ 0 := by
  simp [gaussTest]

theorem norm_gaussTest (t : ℝ) : ‖gaussTest t‖ = Real.exp (-t ^ 2) := by
  rw [gaussTest, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]



open SmoothWindows in
theorem solution: Function.Injective heisRep := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfun : gaborAct g gaussTest = gaussTest := congrFun hg gaussTest
  -- Step 1: `a = 0`, read off from the modulus.
  have hmod : ∀ t : ℝ, Real.exp (-(t - g.a) ^ 2) = Real.exp (-t ^ 2) := by
    intro t
    have h := congrFun hfun t
    rw [gaborAct_apply] at h
    have h' := congrArg (‖·‖) h
    simpa [norm_gaussTest, norm_chi, Complex.norm_mul, Circle.norm_coe] using h'
  have ha : g.a = 0 := by
    have h1 := hmod 0
    have h2 := hmod g.a
    rw [Real.exp_eq_exp] at h1 h2
    nlinarith [h1, h2]
  -- Step 2: the remaining identity is `z·χ(bt) = 1` for all `t`.
  have hphase : ∀ t : ℝ, (g.z : ℂ) * chi (g.b * t) = 1 := by
    intro t
    have h := congrFun hfun t
    rw [gaborAct_apply, ha, sub_zero] at h
    have hne : gaussTest t ≠ 0 := gaussTest_ne_zero t
    have : (g.z : ℂ) * chi (g.b * t) * gaussTest t = 1 * gaussTest t := by
      rw [one_mul]; exact h
    exact mul_right_cancel₀ hne this
  have hz : (g.z : ℂ) = 1 := by simpa using hphase 0
  have hb : g.b = 0 := by
    by_contra hb0
    have h := hphase (1 / (4 * g.b))
    rw [hz, one_mul, show g.b * (1 / (4 * g.b)) = 1 / 4 by field_simp] at h
    exact chi_quarter_ne_one h
  exact Heis.ext ha hb (by ext; simpa using hz)
