-- Prove2me | Definitions.Def_Shared_CyclicTypeChannelCRTLaw
-- name    : Shared_CyclicTypeChannelCRTLaw
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:49:54.182329+00:00
-- url     : https://prove2.me/theorems/38c06e02-ad8e-41f7-8b99-de24f45da518
-- title:
--   Aether Catalog definitions — Shared_CyclicTypeChannelCRTLaw
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CyclicTypeChannelCRTLaw`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CyclicTypeChannelCRTLaw.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelSymmetry
/-
# The CRT additivity law for the splitting-type channel

The exact evaluations show an arithmetic law behind the numbers: for coprime
cyclic orders the type-pair channel is *additive*,

  `I_pair (m * n) = I_pair m + I_pair n`.

This file proves the law in general (for the ordered type pair) from three
ingredients:

* the Chinese Remainder Theorem, which relabels the sample set `box (m*n)` as
  the product `box m ×ˢ box n`;
* the multiplicativity of the splitting type,
  `ord_{mn}(a) = ord_m(a) · ord_n(a)`, together with the fact that this
  factorisation is an *injective recoding* of the pair of component types;
* the additivity of the counting channel over independent products
  (`mutInfo_prod`).

The consequence is a structural explanation of the growth table:
the information of a cyclic order is a sum of primary contributions, so the
one-bit binary cap can be exceeded simply by multiplying orders together.
-/

namespace CyclicTypeChannel

open Finset

/-! ## 1. The ordered type-pair channel -/

/-- The **ordered** splitting-type pair `(T(p), T(q))` of a semiprime `N = p q`. -/
def ordPair (n : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (ordType n p.1, ordType n p.2)

/-- The ordered type-pair channel `I((T(p),T(q)) ; N mod f)`. -/
noncomputable def IpairOrd (n : ℕ) : ℝ := mutInfo (box n) (ordPair n) (prodRes n)


/-! ## 2. Multiplicativity of the splitting type -/



/-! ## 3. The CRT relabelling of the sample set -/

/-- The Chinese Remainder relabelling of a pair of exponents mod `m * n`. -/
def crtMap (m n : ℕ) (p : ℕ × ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((p.1 % m, p.2 % m), (p.1 % n, p.2 % n))




/-! ## 4. The additivity law -/


/-! ## 5. From the ordered to the unordered pair -/




/-! ## 6. The channel is determined by its prime-power values -/



end CyclicTypeChannel


