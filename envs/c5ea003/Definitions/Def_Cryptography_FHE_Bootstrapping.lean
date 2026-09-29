-- Prove2me | Definitions.Def_Cryptography_FHE_Bootstrapping
-- name    : Cryptography_FHE_Bootstrapping
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:42:44.32474+00:00
-- url     : https://prove2.me/theorems/85f5fc7b-a449-407a-bf02-0b2984266063
-- title:
--   Aether Catalog definitions — Cryptography_FHE_Bootstrapping
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.FHE.Bootstrapping`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/FHE/Bootstrapping.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_FHE_NoiseDichotomy
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

namespace FHENoise

open Polynomial

noncomputable section

variable {R : Type*} [CommRing R]

/-! ## 1. Blocks of squarings between refreshes -/

/-- One multiplication level: square, then relinearize. -/
def sqStep (relin : Cipher R → Cipher R) (c : Cipher R) : Cipher R := relin (c * c)

/-- `L` consecutive multiplication levels. -/
def sqBlock (relin : Cipher R → Cipher R) : ℕ → Cipher R → Cipher R
  | 0, c => c
  | (n + 1), c => sqStep relin (sqBlock relin n c)




/-! ## 2. How many levels fit between two bootstraps -/


/-! ## 3. Bootstrapped evaluation of unboundedly deep chains -/

/-- Alternating blocks of `L` multiplication levels with a refresh (bootstrap)
after each block. -/
def bootIter (relin refresh : Cipher R → Cipher R) (L : ℕ) : ℕ → Cipher R → Cipher R
  | 0, c => c
  | (k + 1), c => refresh (sqBlock relin L (bootIter relin refresh L k c))




/-! ## 4. Modulus switching shifts the stability threshold -/


end

end FHENoise


