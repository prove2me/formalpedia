-- Prove2me | solution 1 for KnottedLight.winding_oamPhase
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:28:34.780492+00:00
-- url     : https://prove2.me/submissions/2e80f6b7-6432-4522-80fe-44b733fe6e69

-- Sol generated from Novelty/KnottedLight.lean
import Mathlib
import Definitions.Def_Novelty_KnottedLight
/-
# The Topology of Knotted Light: Winding Number of Orbital-Angular-Momentum Beams

A laser beam carrying orbital angular momentum (OAM) — "knotted light" — has an
azimuthal phase factor `exp(i ℓ θ)`, where the integer `ℓ` is the *topological
charge* of the phase singularity on the beam axis. Physically, `ℓ` counts how many
times the wavefront twists around per wavelength, and it is a robust topological
invariant of the field.

This file gives a self-contained formalization of the topological charge of an OAM
phase field as a genuine **winding number**, defined through the classical contour
integral

        w(φ) = (1 / 2πi) ∮ φ'(θ)/φ(θ) dθ .

## Main results

* `winding_oamPhase`     : the winding number of `exp(i ℓ θ)` is exactly `ℓ`
                           (the deep theorem — charge is the contour integral).
* `winding_quantized`    : the topological charge is always an integer (quantization).
* `oamPhase_mul`         : superposing (multiplying) beams adds their charges.
* `oamPhase_prod`        : conservation of total charge over a family of beams.
* `winding_additive`     : the winding number is additive under charge addition.
* `oamPhase_periodic`    : the phase field is single-valued (2π-periodic).
* `beamAmp_vanishes` /
  `beamAmp_nonzero`      : the amplitude vanishes exactly on the axis (phase
                           singularity) iff the charge is nonzero.

## Contrarian conjectures (v26)

* `winding_can_be_negative` — DISPROOF of "topological charge is always
  nonnegative": vortices of both handedness exist (`ℓ = -1`).
* `oam_annihilation` — DISPROOF of "a product of two vortex beams is again a
  vortex beam": beams of opposite charge `±ℓ` multiply to a nonvanishing constant
  field of winding `0` (the singularities annihilate).
-/

open Complex

open KnottedLight




/-! ## Basic algebra of OAM phases -/






/-! ## The amplitude vanishes exactly on the vortex axis -/



/-! ## The winding number of an OAM beam is its charge -/

/-- The phase field is differentiable, with derivative `i ℓ · exp(i ℓ θ)`. -/
theorem oamPhase_hasDerivAt (ℓ : ℤ) (θ : ℝ) :
    HasDerivAt (oamPhase ℓ) ((ℓ : ℂ) * Complex.I * oamPhase ℓ θ) θ := by
  unfold oamPhase
  have h1 : HasDerivAt (fun t : ℝ => (ℓ : ℂ) * t * Complex.I) ((ℓ : ℂ) * Complex.I) θ := by
    have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) θ := by
      simpa using Complex.ofRealCLM.hasDerivAt
    have h := ((hasDerivAt_const θ (ℓ : ℂ)).mul hid).mul_const Complex.I
    simpa using h
  have h2 := (Complex.hasDerivAt_exp ((ℓ : ℂ) * θ * Complex.I)).comp θ h1
  simpa [mul_comm, mul_left_comm, mul_assoc] using h2

theorem oamPhase_deriv (ℓ : ℤ) (θ : ℝ) :
    deriv (oamPhase ℓ) θ = (ℓ : ℂ) * Complex.I * oamPhase ℓ θ :=
  (oamPhase_hasDerivAt ℓ θ).deriv





/-! ## Contrarian conjectures (v26) -/





open KnottedLight in
theorem solution(ℓ : ℤ) : winding (oamPhase ℓ) = (ℓ : ℂ) := by
  unfold winding
  have hint : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      deriv (oamPhase ℓ) θ / oamPhase ℓ θ = (ℓ : ℂ) * Complex.I := by
    intro θ _
    rw [oamPhase_deriv, mul_div_assoc,
      div_self (by unfold oamPhase; exact Complex.exp_ne_zero _)]
    ring
  rw [intervalIntegral.integral_congr hint, intervalIntegral.integral_const,
    Complex.real_smul]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  push_cast
  field_simp
  ring
