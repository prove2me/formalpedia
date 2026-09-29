-- Prove2me | Definitions.Def_Probability_SharpBridge
-- name    : Probability_SharpBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:36:08.887769+00:00
-- url     : https://prove2.me/theorems/1923aad6-2810-40fe-b5ef-1c9d49be4045
-- title:
--   Aether Catalog definitions — Probability_SharpBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.SharpBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/SharpBridge.lean by skeleton subtraction
import Mathlib

/-!
# The sharp entropy-power / Euclidean-radius bridge

This file isolates the analytic core of the entropy power inequality (EPI).  If `h`
is a differential entropy in dimension `n`, its entropy radius and entropy power are

`r(h) = exp(h/n) / sqrt(2 π e)` and `N(h) = r(h)^2`.

Consequently the sharp EPI is exactly a Pythagorean (Euclidean `ℓ₂`) addition law
for entropy radii.  This is the exponent-two counterpart of the radius formulation
of Brunn--Minkowski.  We prove the equivalence, its exact equality condition, the
sharp isotropic-Gaussian case in every positive dimension, and an exact stability
identity measuring entropy excess above the sharp boundary.
-/

open Real

namespace EntropyPowerInequality

/-- Differential entropy of a centered isotropic Gaussian with scalar variance `v`
in dimension `n`. -/
noncomputable def gaussianEntropy (n : ℕ) (v : ℝ) : ℝ :=
  ((n : ℝ) / 2) * Real.log (2 * Real.pi * Real.exp 1 * v)

/-- Entropy radius. Its normalization makes the radius of an isotropic Gaussian
with variance `v` equal to `sqrt v`. -/
noncomputable def entropyRadius (n : ℕ) (h : ℝ) : ℝ :=
  Real.exp (h / (n : ℝ)) / Real.sqrt (2 * Real.pi * Real.exp 1)

/-- Shannon's entropy power in dimension `n`. -/
noncomputable def entropyPower (n : ℕ) (h : ℝ) : ℝ :=
  Real.exp (2 * h / (n : ℝ)) / (2 * Real.pi * Real.exp 1)

/-- The sharp entropy lower boundary corresponding to two input entropies. -/
noncomputable def sharpEntropyBoundary (n : ℕ) (hX hY : ℝ) : ℝ :=
  ((n : ℝ) / 2) * Real.log
    (Real.exp (2 * hX / (n : ℝ)) + Real.exp (2 * hY / (n : ℝ)))

/-- Entropy-power deficit. EPI says this is nonnegative. -/
noncomputable def epiDeficit (n : ℕ) (hX hY hSum : ℝ) : ℝ :=
  entropyPower n hSum - entropyPower n hX - entropyPower n hY

/-- The geometric `ℓ₂` radius-addition assertion. -/
def PythagoreanRadiusGrowth (rX rY rSum : ℝ) : Prop :=
  rX ^ 2 + rY ^ 2 ≤ rSum ^ 2















end EntropyPowerInequality


