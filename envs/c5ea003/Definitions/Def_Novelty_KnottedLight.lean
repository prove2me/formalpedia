-- Prove2me | Definitions.Def_Novelty_KnottedLight
-- name    : Novelty_KnottedLight
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:31:22.306933+00:00
-- url     : https://prove2.me/theorems/b8327058-f22c-47cd-a0ab-8206151e6847
-- title:
--   Aether Catalog definitions — Novelty_KnottedLight
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.KnottedLight`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/KnottedLight.lean by skeleton subtraction
import Mathlib
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

namespace KnottedLight

/-- The azimuthal phase field of an OAM beam of topological charge `ℓ`:
`θ ↦ exp(i ℓ θ)`. -/
noncomputable def oamPhase (ℓ : ℤ) (θ : ℝ) : ℂ := Complex.exp ((ℓ : ℂ) * θ * Complex.I)

/-- The physical (Laguerre–Gauss–like) amplitude profile, radial factor `r^{|ℓ|}`
times the phase. It vanishes on the axis `r = 0` when `ℓ ≠ 0`, giving the phase
singularity of knotted light. -/
noncomputable def beamAmp (ℓ : ℤ) (r θ : ℝ) : ℂ := (r ^ (ℓ.natAbs) : ℝ) * oamPhase ℓ θ

/-- The winding number of a loop `φ : ℝ → ℂ` computed over one full turn
`θ ∈ [0, 2π]` via the logarithmic-derivative contour integral. -/
noncomputable def winding (φ : ℝ → ℂ) : ℂ :=
  (1 / (2 * Real.pi * Complex.I)) * ∫ θ in (0:ℝ)..(2 * Real.pi), deriv φ θ / φ θ

/-! ## Basic algebra of OAM phases -/






/-! ## The amplitude vanishes exactly on the vortex axis -/



/-! ## The winding number of an OAM beam is its charge -/







/-! ## Contrarian conjectures (v26) -/




end KnottedLight


