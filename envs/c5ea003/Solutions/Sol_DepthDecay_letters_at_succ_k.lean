-- Prove2me | solution 1 for DepthDecay.letters_at_succ_k
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:25:40.756984+00:00
-- url     : https://prove2.me/submissions/5e4b04dc-9d46-424a-84c7-59892deabea7

-- Sol generated from Cryptography/DepthDecay/NullBeyondInversion.lean
import Mathlib
import Definitions.Def_Cryptography_DepthDecay_NullBeyondInversion
import Definitions.Def_Cryptography_DepthDecay_WindowSensor
import Theorems.Thm_DepthDecay_iterate_parent_bigC

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



theorem iter_k_sP {q : ℕ} (hq : 0 < q) (k : ℕ) : parent^[k] (sP q k) = (7 * q + 1, 3 * q) := by
  have hring : (7 + 6 * k) * q = 7 * q + 6 * k * q := by ring
  have hiter := iterate_parent_bigC hq k ((7 + 6 * k) * q + 1) (by omega)
  have hfin : (7 + 6 * k) * q + 1 - 6 * k * q = 7 * q + 1 := by omega
  rw [sP, hiter, hfin]

theorem iter_k_sM {q : ℕ} (hq : 0 < q) (k : ℕ) : parent^[k] (sM q k) = (7 * q - 1, 3 * q) := by
  have hring : (7 + 6 * k) * q = 7 * q + 6 * k * q := by ring
  have hiter := iterate_parent_bigC hq k ((7 + 6 * k) * q - 1) (by omega)
  have hfin : (7 + 6 * k) * q - 1 - 6 * k * q = 7 * q - 1 := by omega
  rw [sM, hiter, hfin]



/-! ### Divergence one step later -/


/-! ### Main theorems -/





/-! ### Sharp threshold, and the surviving `C`-spine -/




open DepthDecay in
theorem solution{q : ℕ} (hq6 : 6 ≤ q) (k : ℕ) :
    letterAt (k + 1) (sP q k) = Letter.B ∧ letterAt (k + 1) (sM q k) = Letter.C := by
  have hq : 0 < q := by omega
  constructor
  · rw [letterAt, Function.iterate_succ_apply', iter_k_sP hq]
    have hA : ¬ (7 * q + 1) < 2 * (3 * q) := by omega
    have hB : (7 * q + 1) < 3 * (3 * q) := by omega
    have hstep : parent (7 * q + 1, 3 * q) = (3 * q, q + 1) := by
      have harith : 7 * q + 1 - 2 * (3 * q) = q + 1 := by omega
      simp only [parent, hA, hB, if_true, if_false, harith]
    rw [hstep]
    have hA2 : ¬ (3 * q) < 2 * (q + 1) := by omega
    have hB2 : (3 * q) < 3 * (q + 1) := by omega
    simp [letterOf, hA2, hB2]
  · rw [letterAt, Function.iterate_succ_apply', iter_k_sM hq]
    have hA : ¬ (7 * q - 1) < 2 * (3 * q) := by omega
    have hB : (7 * q - 1) < 3 * (3 * q) := by omega
    have hstep : parent (7 * q - 1, 3 * q) = (3 * q, q - 1) := by
      have harith : 7 * q - 1 - 2 * (3 * q) = q - 1 := by omega
      simp only [parent, hA, hB, if_true, if_false, harith]
    rw [hstep]
    have hA2 : ¬ (3 * q) < 2 * (q - 1) := by omega
    have hB2 : ¬ (3 * q) < 3 * (q - 1) := by omega
    simp [letterOf, hA2, hB2]
