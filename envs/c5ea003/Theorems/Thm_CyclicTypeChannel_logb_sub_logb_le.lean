-- Prove2me | Theorems.Thm_CyclicTypeChannel_logb_sub_logb_le
-- name    : CyclicTypeChannel.logb_sub_logb_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:22:25.526391+00:00
-- url     : https://prove2.me/theorems/a8f0c868-d7e9-4dad-8d2d-4a597da478f6
-- title:
--   Logb sub logb le
-- statement:
--   Formal statement of `CyclicTypeChannel.logb_sub_logb_le` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem CyclicTypeChannel.logb_sub_logb_le{x : ℝ} (hx : 1 ≤ x) :
--       Real.logb 2 (x + 1) - Real.logb 2 x ≤ 1 / (x * Real.log 2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelPrime.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelPrime.lean#L578

-- Thm stub generated from Shared/CyclicTypeChannelPrime.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannelPrime
/-
# The prime cyclic order: a closed form for the type-pair channel

The exact-value files compute the type-pair channel `Ipair n` for a finite list of
cyclic orders.  This file closes the *prime* case in complete generality: for
every prime `p` the channel of the cyclic order `C p` is

  `Ipair p = log₂ p - (p-1)(2p-1)/p² · log₂ (p-1) + (p-1)(p-2)/p² · log₂ (p-2)`.

(`Ipair_prime`; the two exact values `Ipair 3` and `Ipair 5` recorded in
`CyclicTypeChannelCRT.lean` are the instances `p = 3, 5`.)

Two consequences:

* `Ipair_prime_lt_one`: every **odd** prime order is *strictly below* the one-bit
  binary-fork cap, so among prime cyclic orders the cap is attained exactly at
  `p = 2` (`Ipair_prime_eq_one_iff`).  This upgrades the isolated computations
  `Ipair 3 < 1`, `Ipair 5 < 1` to an infinite statement and shows that the
  above-cap phenomenon of `C₄, C₆, C₁₀, C₁₂, C₁₆` is genuinely a *composite*
  phenomenon: a prime cyclic order has only two splitting types, and its fork is
  exactly the binary fork that papers 72–74 capped.
* `above_cap_imp_not_prime`: breaking the cap forces the cyclic order to be
  composite.
-/

open CyclicTypeChannel

open Finset

/-! ## 1. The splitting type of a prime cyclic order -/





/-! ## 2. The three fibres in the box -/











/-! ## 3. The pair entropy -/



/-! ## 4. The conditional entropy -/











/-! ### The nonzero fibres -/









/-! ## 5. Consequences: the cap among prime orders -/

theorem CyclicTypeChannel.logb_sub_logb_le{x : ℝ} (hx : 1 ≤ x) :
    Real.logb 2 (x + 1) - Real.logb 2 x ≤ 1 / (x * Real.log 2) := by sorry
