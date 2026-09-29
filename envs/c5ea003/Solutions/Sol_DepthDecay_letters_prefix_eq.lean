-- Prove2me | solution 1 for DepthDecay.letters_prefix_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:25:41.810316+00:00
-- url     : https://prove2.me/submissions/7fe96aae-996a-4209-b1ba-adeabd5c3b1a

-- Sol generated from Cryptography/DepthDecay/UniversalNull.lean
import Mathlib
import Definitions.Def_Cryptography_DepthDecay_UniversalNull
import Definitions.Def_Cryptography_DepthDecay_WindowSensor
import Theorems.Thm_DepthDecay_adm_tAbove
import Theorems.Thm_DepthDecay_cRun_letters_C
import Theorems.Thm_DepthDecay_iterate_parent_C_run

/-!
# Every rational-scale magnitude sensor is null beyond the first inversion

`Cryptography.DepthDecay.NullBeyondInversion` defeats the dyadic window sensor
`⌊2^W · m/n⌋`.  One might hope that the failure is an artefact of *binary*
truncation — after all, the offending boundary `7/3` is invisible to base `2` but
plainly visible to base `3`.  This file shows that no change of scale helps.

For arbitrary positive integers `a, b` consider the sensor

  `gprobe a b (m,n) = ⌊(a/b) · (m/n)⌋`,

i.e. any monotone rational rescaling of the magnitude followed by truncation
(`gprobe (2^W) 1 = probe W`).  We prove: **for every scale `a/b` and every depth
`k` the sensor confuses two admissible states which agree on the whole prefix
`C^k B` and differ at depth `k+1`.**

The mechanism is different from — and stronger than — the `7/3` straddle.  Here
the boundary `5/2 + 2k` is *attained* by the admissible state `(4k+5, 2)`, whose
inversion lands exactly on the root; states just above it invert to ratios below
`2` and take the letter `A`.  Since `⌊·⌋` is right-continuous, no truncation
sensor of any scale can separate an attained boundary from its right neighbours.
-/

open DepthDecay





/-! ### Admissibility -/

theorem adm_tBoundary (k : ℕ) : Adm (tBoundary k) := by
  refine ⟨by norm_num [tBoundary], ?_, ?_, ?_⟩
  · show (2 : ℕ) < 4 * k + 5
    omega
  · show Nat.gcd (4 * k + 5) 2 = 1
    have h : (4 * k + 5) % 2 = 1 := by omega
    rw [Nat.gcd_comm, Nat.gcd_rec, h]
    simp
  · show (4 * k + 5 + 2) % 2 = 1
    omega


/-! ### Descent letters of the two states -/

theorem crun_tBoundary (k : ℕ) : ((tBoundary k).1 - (tBoundary k).2) / (2 * (tBoundary k).2) = k := by
  show (4 * k + 5 - 2) / (2 * 2) = k
  omega

theorem crun_tAbove {k u : ℕ} (hu : 2 ≤ u) :
    ((tAbove k u).1 - (tAbove k u).2) / (2 * (tAbove k u).2) = k := by
  show ((4 * k + 5) * u + 1 - 2 * u) / (2 * (2 * u)) = k
  have hd : 2 * (2 * u) = 4 * u := by ring
  have he : (4 * k + 5) * u + 1 - 2 * u = (3 * u + 1) + (4 * u) * k := by
    have : (4 * k + 5) * u = 4 * u * k + 5 * u := by ring
    omega
  rw [hd, he, Nat.add_mul_div_left _ _ (by omega : 0 < 4 * u),
    Nat.div_eq_of_lt (by omega), Nat.zero_add]

theorem iter_tBoundary (k : ℕ) : parent^[k] (tBoundary k) = (5, 2) := by
  have h := iterate_parent_C_run (adm_tBoundary k) k (by rw [crun_tBoundary])
  rw [h]
  show ((4 * k + 5 - 2 * k * 2 : ℕ), (2 : ℕ)) = (5, 2)
  congr 1
  omega

theorem iter_tAbove {k u : ℕ} (hu : 2 ≤ u) (hue : u % 2 = 0) :
    parent^[k] (tAbove k u) = (5 * u + 1, 2 * u) := by
  have h := iterate_parent_C_run (adm_tAbove hu hue) k (by rw [crun_tAbove hu])
  rw [h]
  show (((4 * k + 5) * u + 1 - 2 * k * (2 * u) : ℕ), (2 * u : ℕ)) = (5 * u + 1, 2 * u)
  congr 1
  have : (4 * k + 5) * u = 2 * k * (2 * u) + 5 * u := by ring
  omega



/-! ### The sensor cannot separate them -/


/-! ### Main theorem -/




open DepthDecay in
theorem solution{k u : ℕ} (hu : 2 ≤ u) (hue : u % 2 = 0) :
    ∀ j ≤ k, letterAt j (tBoundary k) = letterAt j (tAbove k u) := by
  intro j hj
  rcases lt_or_eq_of_le hj with h | h
  · rw [cRun_letters_C (adm_tBoundary k) j (by rw [crun_tBoundary]; exact h),
      cRun_letters_C (adm_tAbove hu hue) j (by rw [crun_tAbove hu]; exact h)]
  · subst h
    rw [letterAt, letterAt, iter_tBoundary, iter_tAbove hu hue]
    have h1 : ¬ (5 : ℕ) < 2 * 2 := by omega
    have h2 : (5 : ℕ) < 3 * 2 := by omega
    have h3 : ¬ (5 * u + 1) < 2 * (2 * u) := by omega
    have h4 : (5 * u + 1) < 3 * (2 * u) := by omega
    simp [letterOf, h1, h2, h3, h4]
