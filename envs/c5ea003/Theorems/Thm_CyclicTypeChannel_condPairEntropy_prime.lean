-- Prove2me | Theorems.Thm_CyclicTypeChannel_condPairEntropy_prime
-- name    : CyclicTypeChannel.condPairEntropy_prime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:28:04.541205+00:00
-- url     : https://prove2.me/theorems/c6fb1c4c-e52a-4b44-8408-d3657ef79626
-- title:
--   The conditional pair entropy of a prime cyclic order.
-- statement:
--   **The conditional pair entropy of a prime cyclic order.**
--
--   ```lean
--   theorem CyclicTypeChannel.condPairEntropy_prime{p : ℕ} (hp : p.Prime) :
--       condPairEntropy p = Real.logb 2 p
--         - ((p : ℝ) - 1) * Real.logb 2 ((p : ℝ) - 1) / (p : ℝ) ^ 2
--         - 2 * ((p : ℝ) - 1) / (p : ℝ) ^ 2
--         - ((p : ℝ) - 1) * ((p : ℝ) - 2) * Real.logb 2 ((p : ℝ) - 2) / (p : ℝ) ^ 2 := by sorry
--
--   /-! ## 5. Consequences: the cap among prime orders -/
--
--
--
--
--
--
--
--   /-! ## 6. Cross-checks against the enumerated values
--
--   `Ipair 3` and `Ipair 5` were computed in `CyclicTypeChannelCRT.lean` by explicit
--   enumeration of the `9`- and `25`-element boxes.  Re-deriving them from the general
--   prime formula is an independent check of the closed form. -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelPrime.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelPrime.lean#L519

-- Thm stub generated from Shared/CyclicTypeChannelPrime.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
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

theorem CyclicTypeChannel.condPairEntropy_prime{p : ℕ} (hp : p.Prime) :
    condPairEntropy p = Real.logb 2 p
      - ((p : ℝ) - 1) * Real.logb 2 ((p : ℝ) - 1) / (p : ℝ) ^ 2
      - 2 * ((p : ℝ) - 1) / (p : ℝ) ^ 2
      - ((p : ℝ) - 1) * ((p : ℝ) - 2) * Real.logb 2 ((p : ℝ) - 2) / (p : ℝ) ^ 2 := by sorry
