-- Prove2me | solution 1 for DepthDecay.straddle_collision
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:30:05.809758+00:00
-- url     : https://prove2.me/submissions/92849d8c-5f80-40f1-b717-5941ca444fca

-- Sol generated from Cryptography/DepthDecay/NullBeyondInversion.lean
import Mathlib
import Definitions.Def_Cryptography_DepthDecay_NullBeyondInversion
import Definitions.Def_Cryptography_DepthDecay_WindowSensor
import Theorems.Thm_DepthDecay_adm_add_one
import Theorems.Thm_DepthDecay_adm_sub_one
import Theorems.Thm_DepthDecay_iterate_parent_bigC
import Theorems.Thm_DepthDecay_letters_at_succ_k
import Theorems.Thm_DepthDecay_probe_sP_eq_sM

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



theorem adm_sP {q : ℕ} (hq6 : 6 ≤ q) (h2 : 2 ∣ q) (h3 : 3 ∣ q) (k : ℕ) : Adm (sP q k) :=
  adm_add_one hq6 h2 h3 (by omega)

theorem adm_sM {q : ℕ} (hq6 : 6 ≤ q) (h2 : 2 ∣ q) (h3 : 3 ∣ q) (k : ℕ) : Adm (sM q k) :=
  adm_sub_one hq6 h2 h3 (by omega)



/-! ### The window sensor cannot separate the pair -/


/-! ### The common prefix `C^k B` -/


/-- A state with denominator `3q` whose numerator is still above `9q` has letter `C`. -/
theorem letterAt_C_of_big {q : ℕ} (hq : 0 < q) {m j : ℕ}
    (hm : 9 * q + 6 * j * q < m) : letterAt j (m, 3 * q) = Letter.C := by
  have hiter := iterate_parent_bigC hq j m (by omega)
  have hA : ¬ (m - 6 * j * q) < 2 * (3 * q) := by omega
  have hB : ¬ (m - 6 * j * q) < 3 * (3 * q) := by omega
  simp [letterAt, hiter, letterOf, hA, hB]

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

/-- Both straddling states have letter `C` at every depth below `k`. -/
theorem letters_prefix_C {q : ℕ} (hq : 0 < q) (k : ℕ) :
    ∀ j < k, letterAt j (sP q k) = Letter.C ∧ letterAt j (sM q k) = Letter.C := by
  intro j hj
  have hring : (7 + 6 * k) * q = 7 * q + 6 * k * q := by ring
  have hmul : 6 * (j + 1) * q ≤ 6 * k * q := Nat.mul_le_mul_right _ (by omega)
  have hexp : 6 * (j + 1) * q = 6 * j * q + 6 * q := by ring
  exact ⟨letterAt_C_of_big hq (m := (7 + 6 * k) * q + 1) (by omega),
         letterAt_C_of_big hq (m := (7 + 6 * k) * q - 1) (by omega)⟩

/-- At depth `k` both states perform the same inversion, letter `B`. -/
theorem letters_at_k {q : ℕ} (hq6 : 6 ≤ q) (k : ℕ) :
    letterAt k (sP q k) = Letter.B ∧ letterAt k (sM q k) = Letter.B := by
  have hq : 0 < q := by omega
  constructor
  · rw [letterAt, iter_k_sP hq]
    have hA : ¬ (7 * q + 1) < 2 * (3 * q) := by omega
    have hB : (7 * q + 1) < 3 * (3 * q) := by omega
    simp [letterOf, hA, hB]
  · rw [letterAt, iter_k_sM hq]
    have hA : ¬ (7 * q - 1) < 2 * (3 * q) := by omega
    have hB : (7 * q - 1) < 3 * (3 * q) := by omega
    simp [letterOf, hA, hB]

/-! ### Divergence one step later -/


/-! ### Main theorems -/





/-! ### Sharp threshold, and the surviving `C`-spine -/




open DepthDecay in
theorem solution{W q : ℕ} (hq6 : 6 ≤ q) (h2 : 2 ∣ q) (h3 : 3 ∣ q)
    (hMq : 2 ^ W < q) (k : ℕ) :
    Adm (sP q k) ∧ Adm (sM q k) ∧ probe W (sP q k) = probe W (sM q k) ∧
      (∀ j ≤ k, letterAt j (sP q k) = letterAt j (sM q k)) ∧
      letterAt (k + 1) (sP q k) ≠ letterAt (k + 1) (sM q k) := by
  have hq : 0 < q := by omega
  refine ⟨adm_sP hq6 h2 h3 k, adm_sM hq6 h2 h3 k, probe_sP_eq_sM hq hMq k, ?_, ?_⟩
  · intro j hj
    rcases lt_or_eq_of_le hj with h | h
    · obtain ⟨h1, h2⟩ := letters_prefix_C hq k j h
      rw [h1, h2]
    · subst h
      obtain ⟨h1, h2⟩ := letters_at_k hq6 j
      rw [h1, h2]
  · obtain ⟨h1, h2⟩ := letters_at_succ_k hq6 k
    rw [h1, h2]
    exact fun h => Letter.noConfusion h
