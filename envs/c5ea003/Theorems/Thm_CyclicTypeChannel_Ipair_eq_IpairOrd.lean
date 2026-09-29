-- Prove2me | Theorems.Thm_CyclicTypeChannel_Ipair_eq_IpairOrd
-- name    : CyclicTypeChannel.Ipair_eq_IpairOrd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:27:26.298287+00:00
-- url     : https://prove2.me/theorems/094bb05d-c6b1-4532-92b3-3721f4721a02
-- title:
--   The which-factor wall is exactly zero for the type-pair channel: the
-- statement:
--   **The which-factor wall is exactly zero for the type-pair channel**: the
--   unordered type pair carries exactly as much information about `N mod f` as the
--   ordered one, even though it has strictly smaller entropy whenever the two types
--   can differ.
--
--   ```lean
--   theorem CyclicTypeChannel.Ipair_eq_IpairOrd(n : ℕ) : Ipair n = IpairOrd n := by sorry
--
--   /-! ## 6. The channel is determined by its prime-power values -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelCRTLaw.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelCRTLaw.lean#L177

-- Thm stub generated from Shared/CyclicTypeChannelCRTLaw.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
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


/-! ## 5. From the ordered to the unordered pair -/

theorem CyclicTypeChannel.Ipair_eq_IpairOrd(n : ℕ) : Ipair n = IpairOrd n := by sorry
