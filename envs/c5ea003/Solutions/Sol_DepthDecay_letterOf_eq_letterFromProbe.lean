-- Prove2me | solution 1 for DepthDecay.letterOf_eq_letterFromProbe
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:19:37.471069+00:00
-- url     : https://prove2.me/submissions/e3491a7a-955c-4674-9c8e-57a26e91097e

-- Sol generated from Cryptography/DepthDecay/WindowSensor.lean
import Mathlib
import Definitions.Def_Cryptography_DepthDecay_WindowSensor

/-!
# Depth decay of the magnitude channel on the Berggren / Pythagorean tree

## Setting

Primitive Pythagorean triples are in bijection with *admissible pairs* `(m, n)` of
naturals: `0 < n < m`, `gcd m n = 1`, `m + n` odd.  Berggren's ternary tree on
primitive triples becomes, in these coordinates, the ternary tree on admissible
pairs with children

* `A : (m, n) ↦ (2m - n, m)`,
* `B : (m, n) ↦ (2m + n, m)`,
* `C : (m, n) ↦ (m + 2n, n)`,

rooted at `(2,1)` (the triple `(3,4,5)`).  Inverting, every non-root admissible
pair has a unique *parent*, and which of the three inverse branches applies is
decided purely by the position of the **ratio** `r = m/n` relative to the two
cut points `2` and `3`:

* `r < 2`     → letter `A`, parent `(n, 2n - m)` (parent ratio `1/(2-r)`),
* `2 < r < 3` → letter `B`, parent `(n, m - 2n)` (parent ratio `1/(r-2)`),
* `3 < r`     → letter `C`, parent `(m - 2n, n)` (parent ratio `r - 2`).

This is a Gauss-map style digit expansion of the ratio `r`.

## The sensor model

A *W-window sensor* is the computable functional `probe W (m,n) = ⌊2^W · m / n⌋`:
it reads the magnitude of the ratio to `W` binary places and nothing else, with
a budget independent of the depth of the state in the tree.  This file proves
exactly how far down the descent such a sensor can see.

## Main results (this file)

* `letterOf_eq_letterFromProbe` : the **first** letter is an explicit function of
  the one-bit probe `⌊2m/n⌋`.  The magnitude channel really exists at depth 1.
* `probe_one_parent_of_C` : along a `C`-step the probe merely shifts by `4`.
* `letterAt_eq_of_probe_one_of_prefix_C` : if two admissible states share the
  one-bit probe, then all of their letters agree up to *and including* the first
  non-`C` letter.  The readable prefix is the leading `C`-run plus one inversion
  letter.
* `cRun_letters_C`, `cRun_letterAt_ne_C` : the length of that leading `C`-run is
  the single integer division `(m - n) / (2n)`; depth itself is therefore visible
  to the magnitude channel.

The complementary **null** result — no fixed window can read the letter
immediately after the first inversion, at any prescribed depth — is
`Cryptography.DepthDecay.NullBeyondInversion`.
-/

open DepthDecay









/-! ### Basic structure of admissible states -/


/-- For an admissible state the ratio is never exactly `3`: parity forbids it. -/
theorem ne_three_mul {s : ℕ × ℕ} (h : Adm s) : s.1 ≠ 3 * s.2 := by
  intro hEq
  obtain ⟨hp, _, hg, hpar⟩ := h
  have hdvd : s.2 ∣ s.1 := ⟨3, by omega⟩
  have : Nat.gcd s.1 s.2 = s.2 := Nat.gcd_eq_right hdvd
  have hn : s.2 = 1 := by omega
  omega



/-! ### The channel at depth one: the first letter is a magnitude readout -/






/-! ### Depth itself is visible: the leading `C`-run length is one division -/








open DepthDecay in
theorem solution{s : ℕ × ℕ} (h : Adm s) :
    letterOf s = letterFromProbe (probe 1 s) := by
  obtain ⟨hp, hlt, hg, hpar⟩ := h
  have hAdm : Adm s := ⟨hp, hlt, hg, hpar⟩
  have h3 : s.1 ≠ 3 * s.2 := ne_three_mul hAdm
  have hprobe : probe 1 s = 2 * s.1 / s.2 := by simp [probe, pow_one]
  by_cases hA : s.1 < 2 * s.2
  · have hle : 2 * s.1 / s.2 < 4 := (Nat.div_lt_iff_lt_mul hp).2 (by omega)
    simp [letterOf, letterFromProbe, hprobe, hA, show 2 * s.1 / s.2 ≤ 3 by omega]
  · by_cases hB : s.1 < 3 * s.2
    · have h4 : 4 ≤ 2 * s.1 / s.2 := (Nat.le_div_iff_mul_le hp).2 (by omega)
      have h6 : 2 * s.1 / s.2 < 6 := (Nat.div_lt_iff_lt_mul hp).2 (by omega)
      simp [letterOf, letterFromProbe, hprobe, hA, hB, show ¬ (2 * s.1 / s.2 ≤ 3) by omega,
        show 2 * s.1 / s.2 ≤ 5 by omega]
    · have h6 : 6 ≤ 2 * s.1 / s.2 := (Nat.le_div_iff_mul_le hp).2 (by omega)
      simp [letterOf, letterFromProbe, hprobe, hA, hB, show ¬ (2 * s.1 / s.2 ≤ 3) by omega,
        show ¬ (2 * s.1 / s.2 ≤ 5) by omega]
