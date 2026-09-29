-- Prove2me | Theorems.Thm_FHENoise_bootIter_plain
-- name    : FHENoise.bootIter_plain
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T20:50:14.361124+00:00
-- url     : https://prove2.me/theorems/82a98cdd-452b-40c5-a7bb-dc9c9d74e166
-- title:
--   Plaintext evolution of bootstrapped evaluation: after `k` blocks the
-- statement:
--   Plaintext evolution of bootstrapped evaluation: after `k` blocks the
--   plaintext has been raised to the power `2^(L·k)`.
--
--   ```lean
--   theorem FHENoise.bootIter_plain{M : Type*} [CommRing M] {D T Bref : ℝ} (G : NoiseGauge R) (s : R)
--       (pi : R →+* M) (relin refresh : Cipher R → Cipher R)
--       (hrelin : ∀ c, G.nu (phase s (relin c) - phase s c) ≤ D) (hD : 0 ≤ D)
--       (hrelinP : ∀ c, pi (phase s (relin c)) = pi (phase s c))
--       (hrefN : ∀ c, noise G s c < T → noise G s (refresh c) ≤ Bref)
--       (hrefP : ∀ c, noise G s c < T → pi (phase s (refresh c)) = pi (phase s c))
--       (hBref : 0 ≤ Bref) (L : ℕ) (hsafe : iterD G.gamma D L Bref < T)
--       (c : Cipher R) (hc : noise G s c ≤ Bref) :
--       ∀ k, pi (phase s (bootIter relin refresh L k c)) = (pi (phase s c)) ^ (2 ^ (L * k))
--     := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/FHE/Bootstrapping.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/FHE/Bootstrapping.lean#L130

-- Thm stub generated from Cryptography/FHE/Bootstrapping.lean
import Mathlib
import Definitions.Def_Cryptography_FHE_Bootstrapping
import Definitions.Def_Cryptography_FHE_NoiseDichotomy
import Definitions.Def_Cryptography_FHE_NoiseGauge
import Definitions.Def_Cryptography_FHE_NoiseGrowth

/-!
# Quantitative bootstrapping: unbounded depth at bounded noise

`Cryptography.FHE.RingLWE` states Gentry's bootstrapping principle in an
idealized form: a refresh operation that is *always* correct yields unbounded
depth.  Real bootstrapping is not unconditional — the refresh procedure is
itself a homomorphic evaluation of the decryption circuit, so it only works when
its input is still decryptable, i.e. when the input noise is below the decoding
radius `T`.  This file formalizes exactly that conditional statement and derives
the two quantities a parameter designer actually needs:

* how many multiplication levels `L` fit between two bootstraps
  (`levels_between_bootstraps`, a logarithmic formula), and
* the fact that the *bootstrapped* evaluation of an arbitrarily deep squaring
  chain keeps noise `≤ B_ref` at every stage and decrypts correctly
  (`bootIter_decrypt`).

We also record how modulus switching moves the stability threshold of the
dichotomy of `NoiseDichotomy` (`modSwitch_dichotomy`): dividing the noise by `p`
at each level multiplies the tolerable key-switching noise by `p`.
-/

open FHENoise

-- open removed: section is not a namespace

noncomputable section

variable {R : Type*} [CommRing R]

/-! ## 1. Blocks of squarings between refreshes -/






/-! ## 2. How many levels fit between two bootstraps -/


/-! ## 3. Bootstrapped evaluation of unboundedly deep chains -/

theorem FHENoise.bootIter_plain{M : Type*} [CommRing M] {D T Bref : ℝ} (G : NoiseGauge R) (s : R)
    (pi : R →+* M) (relin refresh : Cipher R → Cipher R)
    (hrelin : ∀ c, G.nu (phase s (relin c) - phase s c) ≤ D) (hD : 0 ≤ D)
    (hrelinP : ∀ c, pi (phase s (relin c)) = pi (phase s c))
    (hrefN : ∀ c, noise G s c < T → noise G s (refresh c) ≤ Bref)
    (hrefP : ∀ c, noise G s c < T → pi (phase s (refresh c)) = pi (phase s c))
    (hBref : 0 ≤ Bref) (L : ℕ) (hsafe : iterD G.gamma D L Bref < T)
    (c : Cipher R) (hc : noise G s c ≤ Bref) :
    ∀ k, pi (phase s (bootIter relin refresh L k c)) = (pi (phase s c)) ^ (2 ^ (L * k))
  := by sorry
