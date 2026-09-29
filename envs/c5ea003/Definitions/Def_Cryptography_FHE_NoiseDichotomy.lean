-- Prove2me | Definitions.Def_Cryptography_FHE_NoiseDichotomy
-- name    : Cryptography_FHE_NoiseDichotomy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:42:05.479328+00:00
-- url     : https://prove2.me/theorems/f800244a-74e6-4c04-9d74-f36157a10c4a
-- title:
--   Aether Catalog definitions — Cryptography_FHE_NoiseDichotomy
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.FHE.NoiseDichotomy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/FHE/NoiseDichotomy.lean by skeleton subtraction
import Mathlib
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

namespace FHENoise

open Polynomial

noncomputable section

/-! ## 1. The quadratic noise map and its orbits -/

/-- One multiplication level: square (paying the expansion factor `γ`), then pay
the relinearization surcharge `D`. -/
def noiseStep (gamma D x : ℝ) : ℝ := gamma * x ^ 2 + D

/-- The noise level after `d` multiplication levels. -/
def iterD (gamma D : ℝ) : ℕ → ℝ → ℝ
  | 0, x => x
  | (d + 1), x => noiseStep gamma D (iterD gamma D d x)





/-! ## 2. The stable regime -/

/-- An **invariant noise budget**: a level that the multiplication step cannot
exceed. -/
def InvariantBudget (gamma D Q : ℝ) : Prop := 0 ≤ Q ∧ noiseStep gamma D Q ≤ Q


/-- The canonical stable budget, the smaller root of `γx² - x + D = 0`. -/
def noiseFixedPoint (gamma D : ℝ) : ℝ := (1 - Real.sqrt (1 - 4 * gamma * D)) / (2 * gamma)


/-! ## 3. The unstable regime -/





/-! ## 3b. Convergence of the stable orbit -/



/-! ## 4. Sharpness: the recursion is attained over `ℤ` -/

namespace NoiseCkt



end NoiseCkt

/-! ## 5. Consequences for homomorphic evaluation -/

variable {R : Type*} [CommRing R]



end

end FHENoise


