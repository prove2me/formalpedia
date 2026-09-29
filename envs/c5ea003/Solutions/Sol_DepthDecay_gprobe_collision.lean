-- Prove2me | solution 1 for DepthDecay.gprobe_collision
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:24:32.241129+00:00
-- url     : https://prove2.me/submissions/859bd61d-b7bb-465a-aa97-051cf5142cea

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
theorem solution{a b k u : ℕ} (ha : 0 < a) (hb : 0 < b) (hau : a < u) :
    gprobe a b (tBoundary k) = gprobe a b (tAbove k u) := by
  set D := 2 * b with hD
  have hDpos : 0 < D := by omega
  have hDu : 0 < D * u := Nat.mul_pos hDpos (by omega)
  set A := a * (4 * k + 5) with hA
  set I := A / D with hI
  set p := A % D with hp
  have hdm : D * I + p = A := by rw [hI, hp]; exact Nat.div_add_mod _ _
  have hplt : p < D := Nat.mod_lt _ hDpos
  have hleft : gprobe a b (tBoundary k) = I := by
    show a * (4 * k + 5) / (b * 2) = I
    rw [show b * 2 = D by rw [hD]; ring, ← hA, hI]
  have hright : gprobe a b (tAbove k u) = I := by
    show a * ((4 * k + 5) * u + 1) / (b * (2 * u)) = I
    have he : a * ((4 * k + 5) * u + 1) = (p * u + a) + (D * u) * I := by
      have h1 : a * ((4 * k + 5) * u + 1) = A * u + a := by rw [hA]; ring
      have h2 : A * u = (D * I + p) * u := by rw [hdm]
      have h3 : (D * I + p) * u = (D * u) * I + p * u := by ring
      omega
    have hlt : p * u + a < D * u := by
      have h1 : p * u + u ≤ D * u := by
        have : (p + 1) * u ≤ D * u := Nat.mul_le_mul_right u (by omega)
        nlinarith [this]
      omega
    rw [show b * (2 * u) = D * u by rw [hD]; ring, he,
      Nat.add_mul_div_left _ _ hDu, Nat.div_eq_of_lt hlt, Nat.zero_add]
  rw [hleft, hright]
