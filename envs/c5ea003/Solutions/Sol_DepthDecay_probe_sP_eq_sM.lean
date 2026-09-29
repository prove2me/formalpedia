-- Prove2me | solution 1 for DepthDecay.probe_sP_eq_sM
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:28:23.722225+00:00
-- url     : https://prove2.me/submissions/1f1b5e5f-1137-458f-a1f6-d343f6adc416

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
theorem solution{W q : ℕ} (hqpos : 0 < q) (hMq : 2 ^ W < q) (k : ℕ) :
    probe W (sP q k) = probe W (sM q k) := by
  set M := 2 ^ W with hM
  set K := 7 + 6 * k with hK
  have hMpos : 0 < M := Nat.one_le_two_pow
  -- the residue of `M*K` mod 3 is nonzero
  have h3M : ¬ (3 ∣ M) := by
    intro h
    have := (Nat.prime_three).dvd_of_dvd_pow (n := W) (by simpa [hM] using h)
    omega
  have hK3 : K % 3 = 1 := by omega
  have hMK3 : (M * K) % 3 ≠ 0 := by
    rw [Nat.mul_mod, hK3]
    have : M % 3 ≠ 0 := fun h => h3M (Nat.dvd_of_mod_eq_zero h)
    have : M % 3 < 3 := Nat.mod_lt _ (by norm_num)
    omega
  set t := (M * K) / 3 with ht
  set r := (M * K) % 3 with hr
  have hdm : 3 * t + r = M * K := by rw [ht, hr]; exact Nat.div_add_mod _ _
  have hrlt : r < 3 := Nat.mod_lt _ (by norm_num)
  have hr0 : r ≠ 0 := hMK3
  -- expansion of both numerators around the common quotient `t`
  have hbase : M * (K * q) = 3 * q * t + r * q := by
    calc M * (K * q) = (M * K) * q := by ring
      _ = (3 * t + r) * q := by rw [hdm]
      _ = 3 * q * t + r * q := by ring
  have hKq1 : 1 ≤ K * q := by
    have : 7 * q ≤ K * q := Nat.mul_le_mul_right q (by omega)
    omega
  have hsub : M * (K * q - 1) = M * (K * q) - M := by
    rw [Nat.mul_sub, Nat.mul_one]
  have hlt1 : r * q + M < 3 * q := by
    have h2 : r * q ≤ 2 * q := Nat.mul_le_mul_right q (by omega)
    omega
  have hge : M ≤ r * q := by
    have h1 : 1 * q ≤ r * q := Nat.mul_le_mul_right q (by omega)
    omega
  have hplus : M * ((K * q) + 1) = (r * q + M) + 3 * q * t := by
    have : M * (K * q + 1) = M * (K * q) + M := by ring
    omega
  have hminus : M * (K * q - 1) = (r * q - M) + 3 * q * t := by omega
  have h3q : 0 < 3 * q := by omega
  have e1 : ((r * q + M) + 3 * q * t) / (3 * q) = t := by
    rw [Nat.add_mul_div_left _ _ h3q, Nat.div_eq_of_lt hlt1, Nat.zero_add]
  have e2 : ((r * q - M) + 3 * q * t) / (3 * q) = t := by
    rw [Nat.add_mul_div_left _ _ h3q, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  simp only [probe, sP, sM, ← hM, ← hK]
  rw [hplus, hminus, e1, e2]
