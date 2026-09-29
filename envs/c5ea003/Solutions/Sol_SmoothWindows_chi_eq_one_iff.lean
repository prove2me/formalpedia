-- Prove2me | solution 1 for SmoothWindows.chi_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T21:17:49.776113+00:00
-- url     : https://prove2.me/submissions/ea0a1244-ee78-4448-949d-9f08ee52c1fa

-- Sol generated from Algebra/SmoothWindows/GaborOperators.lean
import Mathlib
import Definitions.Def_Algebra_SmoothWindows_GaborOperators

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










/-! ## Translation and modulation -/












/-! ## The Heisenberg group and the Gabor representation -/


open Heis


noncomputable instance : One Heis := ⟨⟨0, 0, 1⟩⟩

















open SmoothWindows in
theorem solution(x : ℝ) : chi x = 1 ↔ ∃ n : ℤ, x = n := by
  unfold chi
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hn' : ((2 * π * x : ℝ) : ℂ) = (n : ℂ) * (2 * π) := by
      have h := hn
      rw [show (n : ℂ) * (2 * (π : ℂ) * Complex.I) = ((n : ℂ) * (2 * (π : ℂ))) * Complex.I by
        ring] at h
      exact mul_right_cancel₀ Complex.I_ne_zero h
    have h3 : 2 * π * x = (n : ℝ) * (2 * π) := by exact_mod_cast hn'
    have hpi : (2 * π : ℝ) ≠ 0 := by positivity
    exact mul_left_cancel₀ hpi (by linarith)
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩
