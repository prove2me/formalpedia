-- Prove2me | Theorems.Thm_DepthDecay_straddle_collision
-- name    : DepthDecay.straddle_collision
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:48:23.737771+00:00
-- url     : https://prove2.me/theorems/21f0b2a1-bdab-4e5a-b820-a10af0379aa4
-- title:
--   The straddling pair at any admissible scale is a `W`-window collision that
-- statement:
--   The straddling pair at any admissible scale is a `W`-window collision that
--   diverges exactly one step after the inversion.
--
--   ```lean
--   theorem DepthDecay.straddle_collision{W q : ℕ} (hq6 : 6 ≤ q) (h2 : 2 ∣ q) (h3 : 3 ∣ q)
--       (hMq : 2 ^ W < q) (k : ℕ) :
--       Adm (sP q k) ∧ Adm (sM q k) ∧ probe W (sP q k) = probe W (sM q k) ∧
--         (∀ j ≤ k, letterAt j (sP q k) = letterAt j (sM q k)) ∧
--         letterAt (k + 1) (sP q k) ≠ letterAt (k + 1) (sM q k) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/DepthDecay/NullBeyondInversion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/DepthDecay/NullBeyondInversion.lean#L311

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

theorem DepthDecay.straddle_collision{W q : ℕ} (hq6 : 6 ≤ q) (h2 : 2 ∣ q) (h3 : 3 ∣ q)
    (hMq : 2 ^ W < q) (k : ℕ) :
    Adm (sP q k) ∧ Adm (sM q k) ∧ probe W (sP q k) = probe W (sM q k) ∧
      (∀ j ≤ k, letterAt j (sP q k) = letterAt j (sM q k)) ∧
      letterAt (k + 1) (sP q k) ≠ letterAt (k + 1) (sM q k) := by sorry
