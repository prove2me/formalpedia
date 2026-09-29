-- Prove2me | Theorems.Thm_KnottedLight_winding_oamPhase
-- name    : KnottedLight.winding_oamPhase
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:05:30.568475+00:00
-- url     : https://prove2.me/theorems/de8ce921-6f26-4522-9845-b1fd2d360510
-- title:
--   Topological charge = winding number.
-- statement:
--   **Topological charge = winding number.** The contour-integral winding number of
--   `exp(i ℓ θ)` is exactly the integer charge `ℓ`.
--
--   ```lean
--   theorem KnottedLight.winding_oamPhase(ℓ : ℤ) : winding (oamPhase ℓ) = (ℓ : ℂ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/KnottedLight.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/KnottedLight.lean#L122

-- Thm stub generated from Novelty/KnottedLight.lean
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

theorem KnottedLight.winding_oamPhase(ℓ : ℤ) : winding (oamPhase ℓ) = (ℓ : ℂ) := by sorry
