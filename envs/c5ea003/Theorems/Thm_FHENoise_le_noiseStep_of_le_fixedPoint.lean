-- Prove2me | Theorems.Thm_FHENoise_le_noiseStep_of_le_fixedPoint
-- name    : FHENoise.le_noiseStep_of_le_fixedPoint
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T20:53:20.639231+00:00
-- url     : https://prove2.me/theorems/e248de4e-d521-4bdd-8fa9-c89e1c28aca1
-- title:
--   Below an exact fixed point the noise map is increasing: the orbit climbs
-- statement:
--   Below an exact fixed point the noise map is increasing: the orbit climbs
--   towards the budget instead of oscillating.
--
--   ```lean
--   theorem FHENoise.le_noiseStep_of_le_fixedPoint{gamma D Q y : ℝ} (hg : 0 < gamma)
--       (hQfix : noiseStep gamma D Q = Q) (hQle : Q ≤ 1 / (2 * gamma))
--       (hy : y ≤ Q) : y ≤ noiseStep gamma D y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/FHE/NoiseDichotomy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/FHE/NoiseDichotomy.lean#L177

-- Thm stub generated from Cryptography/FHE/NoiseDichotomy.lean
import Mathlib
import Definitions.Def_Cryptography_FHE_NoiseDichotomy
import Definitions.Def_Cryptography_FHE_NoiseGrowth

/-!
# The bootstrapping dichotomy: when is a levelled FHE scheme noise-stable?

Homomorphic multiplication followed by relinearization transforms the
(normalized) noise level `x` by the quadratic map

`noiseStep γ D x = γ · x² + D`,

where `γ ≥ 1` is the ring expansion factor and `D ≥ 0` is the key-switching
noise surcharge.  Everything about unbounded-depth evaluation is governed by the
orbit structure of this one-dimensional quadratic dynamical system, and the
governing quantity is the discriminant `1 - 4γD`.

## Main results

* `noiseStep_dichotomy` — **the dichotomy**: an invariant noise budget exists
  (i.e. `∃ Q ≥ 0, γQ² + D ≤ Q`) **iff** `4γD ≤ 1`.  There is no middle ground.
* `iterD_le_of_invariant` — inside the stable regime the noise never leaves the
  invariant interval, at *any* multiplicative depth: no bootstrapping needed.
* `noiseFixedPoint_spec` — the explicit stable budget
  `Q = (1 - √(1 - 4γD)) / (2γ)`, an exact fixed point, with `Q ≤ 1/(2γ)`.
* `iterD_ge_linear` and `exists_depth_exceeding` — **bootstrapping necessity**:
  when `4γD > 1` the noise grows at least linearly with slope
  `c = D - 1/(4γ) > 0`, so *every* decryption radius is exceeded after finitely
  many levels, and an explicit depth bound is given.
* `sqChain_noise_eq_iterD` — sharpness: over `ℤ` the recursion is *attained*, so
  the dichotomy is not an artefact of lossy bounding.
* `unbounded_depth_correct` / `bootstrap_needed_at_depth` — the two sides of the
  dichotomy transported back to statements about decrypting circuits.
-/

open FHENoise

-- open removed: section is not a namespace

noncomputable section

/-! ## 1. The quadratic noise map and its orbits -/







/-! ## 2. The stable regime -/





/-! ## 3. The unstable regime -/





/-! ## 3b. Convergence of the stable orbit -/

theorem FHENoise.le_noiseStep_of_le_fixedPoint{gamma D Q y : ℝ} (hg : 0 < gamma)
    (hQfix : noiseStep gamma D Q = Q) (hQle : Q ≤ 1 / (2 * gamma))
    (hy : y ≤ Q) : y ≤ noiseStep gamma D y := by sorry
