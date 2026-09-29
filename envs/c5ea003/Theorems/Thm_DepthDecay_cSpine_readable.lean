-- Prove2me | Theorems.Thm_DepthDecay_cSpine_readable
-- name    : DepthDecay.cSpine_readable
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:47:47.626571+00:00
-- url     : https://prove2.me/theorems/83e43db5-08bb-4347-88fb-6f2aa2314fe8
-- title:
--   The decay is about inversions, not about depth.
-- statement:
--   **The decay is about inversions, not about depth.**  Along the all-`C` spine
--   the one-bit probe reads arbitrarily many letters: the state `(2L+2, 1)` has a
--   leading `C`-run of length `L`, and every admissible state with the same one-bit
--   probe reproduces all of `letterAt 0, …, letterAt L`.
--
--   ```lean
--   theorem DepthDecay.cSpine_readable(L : ℕ) :
--       Adm (2 * L + 2, 1) ∧ (∀ j < L, letterAt j (2 * L + 2, 1) = Letter.C) ∧
--         (∀ s' : ℕ × ℕ, Adm s' → probe 1 (2 * L + 2, 1) = probe 1 s' →
--           ∀ j ≤ L, letterAt j (2 * L + 2, 1) = letterAt j s') := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/DepthDecay/NullBeyondInversion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/DepthDecay/NullBeyondInversion.lean#L383

-- Thm stub generated from Cryptography/DepthDecay/NullBeyondInversion.lean
import Mathlib
import Definitions.Def_Cryptography_DepthDecay_NullBeyondInversion
import Definitions.Def_Cryptography_DepthDecay_WindowSensor

/-!
# The magnitude channel is null beyond the first inversion

`Cryptography.DepthDecay.WindowSensor` shows that a one-bit magnitude probe of an
admissible pair `(m,n)` already determines the whole leading `C`-run of the
Berggren descent *and* the inversion letter that terminates it.  Here we prove
the matching negative statement, which is the formal content of the observed
depth decay of the magnitude channel:

> **No fixed window budget `W` determines the letter that follows the first
> inversion, at any prescribed depth.**

For every window budget `W`, every depth `k` and every admissible scale `q` we
construct two admissible pairs `sP q k` and `sM q k` whose `2^W`-window probes are
*equal*, whose descent paths agree on the whole prefix of length `k+1` (namely
`C^k B`), and which nevertheless differ at depth `k+1`.

The construction is the two sides of the non-dyadic branch boundary `r = 7/3` of
the second Gauss digit:

* `sP q k = ((7+6k)q + 1, 3q)`, ratio `7/3 + 2k + 1/(3q)`,
* `sM q k = ((7+6k)q - 1, 3q)`, ratio `7/3 + 2k - 1/(3q)`.

As soon as `2^W < q` both ratios lie in the same dyadic interval of width `2^{-W}`
— the sensor cannot separate them — yet after the `k` translations `r ↦ r-2` and
the inversion `r ↦ 1/(r-2)` the images straddle the cut point `3`, and the next
letters are `B` and `C` respectively.  The information the sensor would need is
the *fine* Gauss digit of the ratio, which no fixed-precision window supplies.

Because `q` is free, the counterexamples occur at arbitrarily large denominators:
see `depth_null_unbounded`.
-/

open DepthDecay

/-! ### The straddling pair -/
















/-! ### Admissibility of the straddling pair -/







/-! ### The window sensor cannot separate the pair -/


/-! ### The common prefix `C^k B` -/







/-! ### Divergence one step later -/


/-! ### Main theorems -/





/-! ### Sharp threshold, and the surviving `C`-spine -/

theorem DepthDecay.cSpine_readable(L : ℕ) :
    Adm (2 * L + 2, 1) ∧ (∀ j < L, letterAt j (2 * L + 2, 1) = Letter.C) ∧
      (∀ s' : ℕ × ℕ, Adm s' → probe 1 (2 * L + 2, 1) = probe 1 s' →
        ∀ j ≤ L, letterAt j (2 * L + 2, 1) = letterAt j s') := by sorry
