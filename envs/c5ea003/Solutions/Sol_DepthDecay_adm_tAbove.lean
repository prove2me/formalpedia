-- Prove2me | solution 1 for DepthDecay.adm_tAbove
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:16:12.489792+00:00
-- url     : https://prove2.me/submissions/7b1d0f38-f7cd-47d8-8e1d-3307bf36bcd2

-- Sol generated from Cryptography/DepthDecay/UniversalNull.lean
import Mathlib
import Definitions.Def_Cryptography_DepthDecay_UniversalNull
import Definitions.Def_Cryptography_DepthDecay_WindowSensor

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



/-! ### Descent letters of the two states -/







/-! ### The sensor cannot separate them -/


/-! ### Main theorem -/




open DepthDecay in
theorem solution{k u : ℕ} (hu : 2 ≤ u) (hue : u % 2 = 0) : Adm (tAbove k u) := by
  have hmul : 2 ∣ (4 * k + 5) * u := Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero hue) _
  obtain ⟨v, hv⟩ := hmul
  have hbig : 3 * u ≤ (4 * k + 5) * u := Nat.mul_le_mul_right u (by omega)
  refine ⟨by simp [tAbove]; omega, by simp [tAbove]; omega, ?_, by simp [tAbove]; omega⟩
  show Nat.gcd ((4 * k + 5) * u + 1) (2 * u) = 1
  set g := Nat.gcd ((4 * k + 5) * u + 1) (2 * u) with hgdef
  have hg1 : g ∣ (4 * k + 5) * u + 1 := Nat.gcd_dvd_left _ _
  have hg2 : g ∣ 2 * u := Nat.gcd_dvd_right _ _
  have hg2' : g ∣ 2 := by
    have ha : g ∣ 2 * ((4 * k + 5) * u + 1) := hg1.mul_left 2
    have hb : g ∣ (4 * k + 5) * (2 * u) := hg2.mul_left _
    have e : 2 * ((4 * k + 5) * u + 1) = (4 * k + 5) * (2 * u) + 2 := by ring
    rw [e] at ha
    simpa using Nat.dvd_sub ha hb
  have hodd : ((4 * k + 5) * u + 1) % 2 = 1 := by omega
  rcases (Nat.prime_two).eq_one_or_self_of_dvd g hg2' with h | h
  · exact h
  · exfalso
    rw [h] at hg1
    omega
