-- Prove2me | Definitions.Def_Cryptography_DepthDecay_NullBeyondInversion
-- name    : Cryptography_DepthDecay_NullBeyondInversion
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:12:51.816038+00:00
-- url     : https://prove2.me/theorems/d5ef8292-d465-4b5a-a280-3c3c36a733ef
-- title:
--   Aether Catalog definitions — Cryptography_DepthDecay_NullBeyondInversion
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.DepthDecay.NullBeyondInversion`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/DepthDecay/NullBeyondInversion.lean by skeleton subtraction
import Mathlib
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

namespace DepthDecay

/-! ### The straddling pair -/

/-- The state just above the boundary `7/3 + 2k`, at scale `q`. -/
def sP (q k : ℕ) : ℕ × ℕ := ((7 + 6 * k) * q + 1, 3 * q)

/-- The state just below the boundary `7/3 + 2k`, at scale `q`. -/
def sM (q k : ℕ) : ℕ × ℕ := ((7 + 6 * k) * q - 1, 3 * q)

/-- The canonical scale for window budget `W`: `q = 6·2^W`. -/
def qOf (W : ℕ) : ℕ := 6 * 2 ^ W

/-- A scale exceeding any prescribed size `N`, still adapted to budget `W`. -/
def qOfN (W N : ℕ) : ℕ := 6 * 2 ^ W * (N + 1)

/-- The canonical straddling states for budget `W` and depth `k`. -/
def sPlus (W k : ℕ) : ℕ × ℕ := sP (qOf W) k

/-- The canonical straddling states for budget `W` and depth `k`. -/
def sMinus (W k : ℕ) : ℕ × ℕ := sM (qOf W) k










/-! ### Admissibility of the straddling pair -/







/-! ### The window sensor cannot separate the pair -/


/-! ### The common prefix `C^k B` -/







/-! ### Divergence one step later -/


/-! ### Main theorems -/





/-! ### Sharp threshold, and the surviving `C`-spine -/



end DepthDecay


