-- Prove2me | solution 1 for DepthDecay.iterate_parent_bigC
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:24:32.697793+00:00
-- url     : https://prove2.me/submissions/04912653-17ca-4473-aa26-e2a53c75eed1

-- Sol generated from Cryptography/DepthDecay/NullBeyondInversion.lean
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




open DepthDecay in
theorem solution{q : ℕ} (hq : 0 < q) :
    ∀ (j m : ℕ), 9 * q + 6 * j * q < m + 6 * q →
      parent^[j] (m, 3 * q) = (m - 6 * j * q, 3 * q) := by
  intro j
  induction j with
  | zero => intro m _; simp
  | succ j ih =>
    intro m hm
    have hexp : 6 * (j + 1) * q = 6 * j * q + 6 * q := by ring
    have h9 : 9 * q < m := by omega
    have hA : ¬ m < 2 * (3 * q) := by omega
    have hB : ¬ m < 3 * (3 * q) := by omega
    have harith : m - 2 * (3 * q) = m - 6 * q := by omega
    have hstep : parent (m, 3 * q) = (m - 6 * q, 3 * q) := by
      simp only [parent, hA, hB, if_false, harith]
    rw [Function.iterate_succ_apply, hstep, ih (m - 6 * q) (by omega)]
    have hfin : m - 6 * q - 6 * j * q = m - 6 * (j + 1) * q := by omega
    rw [hfin]
