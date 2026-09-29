-- Prove2me | Theorems.Thm_CyclicTypeChannel_IpairOrd_mul_of_coprime
-- name    : CyclicTypeChannel.IpairOrd_mul_of_coprime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:27:11.786983+00:00
-- url     : https://prove2.me/theorems/632f246b-8f6c-4659-9af0-3751e9bea3e2
-- title:
--   CRT additivity of the splitting-type channel.
-- statement:
--   **CRT additivity of the splitting-type channel.**  For coprime cyclic orders
--   the (ordered) type-pair information splits as a sum over the primary components:
--   `I(mÂ·n) = I(m) + I(n)`.  This is the exact law behind the observed values
--   `I(6) = I(2)+I(3)`, `I(10) = I(2)+I(5)`, `I(12) = I(4)+I(3)`,
--   `I(15) = I(3)+I(5)`.
--
--   ```lean
--   theorem CyclicTypeChannel.IpairOrd_mul_of_coprime{m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n) :
--       IpairOrd (m * n) = IpairOrd m + IpairOrd n := by sorry
--   /-! ## 5. From the ordered to the unordered pair -/
--
--
--
--
--   /-! ## 6. The channel is determined by its prime-power values -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelCRTLaw.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelCRTLaw.lean#L104

-- Thm stub generated from Shared/CyclicTypeChannelCRTLaw.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannelCRTLaw
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

open CyclicTypeChannel

open Finset

/-! ## 1. The ordered type-pair channel -/




/-! ## 2. Multiplicativity of the splitting type -/



/-! ## 3. The CRT relabelling of the sample set -/





/-! ## 4. The additivity law -/

theorem CyclicTypeChannel.IpairOrd_mul_of_coprime{m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n) :
    IpairOrd (m * n) = IpairOrd m + IpairOrd n := by sorry
