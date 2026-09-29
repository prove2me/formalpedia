-- Prove2me | solution 1 for DepthDecay.adm_add_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:16:11.23728+00:00
-- url     : https://prove2.me/submissions/756683e2-a814-4486-bf1b-451d3a446db7

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
theorem solution{q K : ℕ} (hq6 : 6 ≤ q) (h2 : 2 ∣ q) (h3 : 3 ∣ q) (hK : 7 ≤ K) :
    Adm (K * q + 1, 3 * q) := by
  obtain ⟨u, hu⟩ := h2
  have hKq : 7 * q ≤ K * q := Nat.mul_le_mul_right q hK
  have hKu : K * q = 2 * (K * u) := by rw [hu]; ring
  refine ⟨by simp; omega, by simp; omega, ?_, by simp; omega⟩
  simp only []
  set g := Nat.gcd (K * q + 1) (3 * q) with hgdef
  have hg1 : g ∣ K * q + 1 := Nat.gcd_dvd_left _ _
  have hg2 : g ∣ 3 * q := Nat.gcd_dvd_right _ _
  have h3Kq : 3 ∣ K * q := Dvd.dvd.mul_left h3 K
  have hg3 : g ∣ 3 := by
    have ha : g ∣ 3 * (K * q + 1) := hg1.mul_left 3
    have hb : g ∣ K * (3 * q) := hg2.mul_left K
    have e : 3 * (K * q + 1) = K * (3 * q) + 3 := by ring
    rw [e] at ha
    simpa using Nat.dvd_sub ha hb
  rcases (Nat.prime_three).eq_one_or_self_of_dvd g hg3 with h | h
  · exact h
  · exfalso
    rw [h] at hg1
    have : (3 : ℕ) ∣ 1 := by simpa using Nat.dvd_sub hg1 h3Kq
    omega
