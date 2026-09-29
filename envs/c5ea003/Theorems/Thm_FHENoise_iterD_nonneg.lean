-- Prove2me | Theorems.Thm_FHENoise_iterD_nonneg
-- name    : FHENoise.iterD_nonneg
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T20:52:40.618118+00:00
-- url     : https://prove2.me/theorems/b52872e6-c515-4ca6-92dc-65483290d11c
-- title:
--   IterD nonneg
-- statement:
--   Formal statement of `FHENoise.iterD_nonneg` from the Aether Catalog (Cryptography). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem FHENoise.iterD_nonneg{gamma D x : ℝ} (hg : 0 ≤ gamma) (hD : 0 ≤ D) (hx : 0 ≤ x) :
--       ∀ d, 0 ≤ iterD gamma D d x
--     := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/FHE/NoiseDichotomy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/FHE/NoiseDichotomy.lean#L55

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

theorem FHENoise.iterD_nonneg{gamma D x : ℝ} (hg : 0 ≤ gamma) (hD : 0 ≤ D) (hx : 0 ≤ x) :
    ∀ d, 0 ≤ iterD gamma D d x
  := by sorry
