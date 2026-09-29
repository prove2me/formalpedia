-- Prove2me | Theorems.Thm_DepthDecay_iterate_parent_bigC
-- name    : DepthDecay.iterate_parent_bigC
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:48:17.17968+00:00
-- url     : https://prove2.me/theorems/19a35f6d-c799-472d-b51a-b979bf520ba6
-- title:
--   Iterating the `C`-branch on states with denominator `3q`.
-- statement:
--   Iterating the `C`-branch on states with denominator `3q`.
--
--   ```lean
--   theorem DepthDecay.iterate_parent_bigC{q : ℕ} (hq : 0 < q) :
--       ∀ (j m : ℕ), 9 * q + 6 * j * q < m + 6 * q →
--         parent^[j] (m, 3 * q) = (m - 6 * j * q, 3 * q) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/DepthDecay/NullBeyondInversion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/DepthDecay/NullBeyondInversion.lean#L216

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

theorem DepthDecay.iterate_parent_bigC{q : ℕ} (hq : 0 < q) :
    ∀ (j m : ℕ), 9 * q + 6 * j * q < m + 6 * q →
      parent^[j] (m, 3 * q) = (m - 6 * j * q, 3 * q) := by sorry
