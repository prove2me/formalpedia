-- Prove2me | Theorems.Thm_CyclicTypeChannel_Ipair_prime_le_envelope
-- name    : CyclicTypeChannel.Ipair_prime_le_envelope
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:28:32.25124+00:00
-- url     : https://prove2.me/theorems/dc2dbcd6-1d5f-467d-8c17-7b3b90d18096
-- title:
--   The prime channel decays: an explicit envelope `Ipair p â¤ (logâ p + 3p)/pÂ²`
-- statement:
--   The prime channel decays: an explicit envelope `Ipair p â¤ (logâ p + 3p)/pÂ²`
--   for every prime `p`, so the prime-order channel tends to `0`.
--
--   ```lean
--   theorem CyclicTypeChannel.Ipair_prime_le_envelope{p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
--       Ipair p ≤ (Real.logb 2 (p : ℝ) + 3 * (p : ℝ)) / (p : ℝ) ^ 2 := by sorry
--   /-! ## 6. Cross-checks against the enumerated values
--
--   `Ipair 3` and `Ipair 5` were computed in `CyclicTypeChannelCRT.lean` by explicit
--   enumeration of the `9`- and `25`-element boxes.  Re-deriving them from the general
--   prime formula is an independent check of the closed form. -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelPrime.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelPrime.lean#L713

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









/-! ## 5. Consequences: the cap among prime orders -/

theorem CyclicTypeChannel.Ipair_prime_le_envelope{p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Ipair p ≤ (Real.logb 2 (p : ℝ) + 3 * (p : ℝ)) / (p : ℝ) ^ 2 := by sorry
