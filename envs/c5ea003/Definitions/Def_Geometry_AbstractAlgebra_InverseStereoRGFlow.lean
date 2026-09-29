-- Prove2me | Definitions.Def_Geometry_AbstractAlgebra_InverseStereoRGFlow
-- name    : Geometry_AbstractAlgebra_InverseStereoRGFlow
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:34:19.702617+00:00
-- url     : https://prove2.me/theorems/49d29012-d351-4695-b603-251b1592b81a
-- title:
--   Aether Catalog definitions — Geometry_AbstractAlgebra_InverseStereoRGFlow
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.AbstractAlgebra.InverseStereoRGFlow`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/AbstractAlgebra/InverseStereoRGFlow.lean by skeleton subtraction
import Mathlib

/-! # Inverse Stereographic Renormalization Group

The renormalization group (RG) in physics "zooms out" by rescaling energy/length
scales.  Here we formalize the slogan

> *RG flow = iterated inverse stereographic projection on the energy sphere.*

The line `ℝ` is the space of (signed log-)energy coordinates `t`.  Inverse
stereographic projection `invStereo : ℝ → S¹ ⊂ ℝ²` wraps the line onto the
energy circle, sending `0 ↦ (0,1)` (the UV fixed point) and `t → ∞ ↦ (0,-1)`
(the IR fixed point).  Multiplicative rescaling `t ↦ λ·t` is the RG dilation on
the line; conjugating it by stereographic projection yields the **RG flow on the
circle** `rgFlow λ`.  The headline result `rgFlow_iterate` shows that iterating
the flow `n` times multiplies the scale by `λ^n` — exactly the one-parameter
(semi)group structure that *defines* a renormalization group.

This file is fully self-contained: it redefines `invStereo`/`stereoProj` so it
does not depend on the (currently non-compiling) auto-generated catalog stubs in
`Catalog/Geometry/InverseStereoResearch.lean` and
`Catalog/Computation/Oracles/Foundation.lean`, while reproving and *extending*
their core facts (`inv_stereo_on_circle`, `stereo_left_inverse`).

-- !-- Lab Notebook -- !--
Hypothesis: The physicists' RG semigroup is, up to a conjugacy, nothing more
  than multiplicative scaling of a real coordinate; stereographic projection
  realizes this conjugacy geometrically on a sphere/circle.
Result: Proven. `rgFlow λ` conjugates the dilation `t ↦ λt`, the conjugacy is
  exact on the image circle (`rgFlow_invStereo`), the flow is a semigroup
  (`rgFlow_semigroup`), it preserves the circle (`rgFlow_on_circle`), iterating
  it `n` times scales by `λ^n` (`rgFlow_iterate`), `(0,1)` is a universal fixed
  point (`rgFlow_uv_fixed`), and the IR endpoint `(0,-1)` is the `atTop` limit
  (`invStereo_tendsto_IR`).
Insight: The RG "loss of information when integrating out high modes" is *not*
  present at the level of the bijection — `invStereo` is injective with explicit
  inverse `stereoProj`.  Irreversibility only appears in the *iterated limit*
  λ^n → 0 or ∞, where every trajectory collapses onto a fixed point.  Thus RG
  irreversibility is a statement about the asymptotics of the abelian flow, not
  about the maps themselves.
Failure analysis: An earlier attempt tried to put the IR fixed point as an
  algebraic identity `rgFlow λ (0,-1) = (0,-1)`; this fails because `stereoProj`
  has a pole at the north pole `(0,-1)` (denominator `1 + y = 0`), so the IR
  fixed point is genuinely a *boundary/limit* object, captured correctly by a
  `Filter.Tendsto` statement rather than an equation.
-/

noncomputable section

namespace InverseStereoRG

/-- Inverse stereographic projection of the energy line onto the unit circle
`S¹ ⊂ ℝ²`. The parameter `t` is the energy coordinate. -/
def invStereo (t : ℝ) : ℝ × ℝ := (2 * t / (1 + t ^ 2), (1 - t ^ 2) / (1 + t ^ 2))

/-- Stereographic projection back to the line, from the north pole `(0,-1)`.
It is a left inverse of `invStereo` (see `stereoProj_invStereo`). -/
def stereoProj (p : ℝ × ℝ) : ℝ := p.1 / (1 + p.2)

-- !-- The image of `invStereo` lies on `S¹`: clear denominators and `ring`. -- !--

-- !-- `stereoProj ∘ invStereo = id`: field_simp collapses the nested fraction. -- !--

-- !-- Injectivity follows from the explicit left inverse. -- !--

/-- The RG dilation on the energy line: multiplicative rescaling by `l`. -/
def dilate (l t : ℝ) : ℝ := l * t

/-- The **renormalization-group flow on the energy circle**: conjugate the line
dilation `dilate l` by stereographic projection. -/
def rgFlow (l : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := invStereo (dilate l (stereoProj p))

-- !-- Unfold `rgFlow`, then `stereoProj_invStereo` cancels projection∘injection. -- !--

-- !-- Image of `rgFlow` is again an `invStereo` value, hence on the circle. -- !--

-- !-- Apply the conjugacy identity three times; `mul_assoc` matches the scales. -- !--

-- !-- Induction on `n`; the successor step uses `rgFlow_invStereo` then `ring_nf`. -- !--

-- !-- Scaling fixes `t = 0`; `mul_zero` then the conjugacy identity. -- !--

/-
!-- Componentwise limits: `2t/(1+t²)→0` and `(1-t²)/(1+t²)→-1` as `t→∞`. -- !--

**IR fixed point as a limit.** As the energy coordinate runs to infinity the
RG trajectory collapses onto the north pole `(0,-1)`, the infrared fixed point.
This is a genuine boundary/limit phenomenon (`stereoProj` has a pole there), the
geometric face of RG irreversibility.
-/

end InverseStereoRG


