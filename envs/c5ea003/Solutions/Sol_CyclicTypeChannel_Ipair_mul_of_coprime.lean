-- Prove2me | solution 1 for CyclicTypeChannel.Ipair_mul_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:30:41.837493+00:00
-- url     : https://prove2.me/submissions/6a57fd7f-69b3-4b42-a6a2-b8bd2687377e

-- Sol generated from Shared/CyclicTypeChannelCRTLaw.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelCRTLaw
import Definitions.Def_Shared_CyclicTypeChannelSymmetry
import Theorems.Thm_CyclicTypeChannel_IpairOrd_mul_of_coprime
import Theorems.Thm_CyclicTypeChannel_Ipair_eq_IpairOrd
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

open CyclicTypeChannel

open Finset

/-! ## 1. The ordered type-pair channel -/




/-! ## 2. Multiplicativity of the splitting type -/



/-! ## 3. The CRT relabelling of the sample set -/





/-! ## 4. The additivity law -/


/-! ## 5. From the ordered to the unordered pair -/




/-! ## 6. The channel is determined by its prime-power values -/




open CyclicTypeChannel in
theorem solution{m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n) :
    Ipair (m * n) = Ipair m + Ipair n := by
  rw [Ipair_eq_IpairOrd, Ipair_eq_IpairOrd, Ipair_eq_IpairOrd, IpairOrd_mul_of_coprime hm hn h]
