-- Prove2me | Theorems.Thm_EntropyPowerInequality_epi_equality_iff_entropy_boundary
-- name    : EntropyPowerInequality.epi_equality_iff_entropy_boundary
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:20:50.115179+00:00
-- url     : https://prove2.me/theorems/cceca105-bcb6-4073-9562-8942d04a58a4
-- title:
--   The exact equality case: the output entropy power is the sum of input powers
-- statement:
--   The exact equality case: the output entropy power is the sum of input powers
--   if and only if output entropy lies on the sharp logarithmic boundary.
--
--   ```lean
--   theorem EntropyPowerInequality.epi_equality_iff_entropy_boundary{n : ℕ} (hn : 0 < n)
--       (hX hY hSum : ℝ) :
--       entropyPower n hSum = entropyPower n hX + entropyPower n hY ↔
--         hSum = sharpEntropyBoundary n hX hY := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/SharpBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/SharpBridge.lean#L90

-- Thm stub generated from Probability/SharpBridge.lean
import Mathlib
import Definitions.Def_Probability_SharpBridge

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

open EntropyPowerInequality

theorem EntropyPowerInequality.epi_equality_iff_entropy_boundary{n : ℕ} (hn : 0 < n)
    (hX hY hSum : ℝ) :
    entropyPower n hSum = entropyPower n hX + entropyPower n hY ↔
      hSum = sharpEntropyBoundary n hX hY := by sorry
