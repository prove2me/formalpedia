-- Prove2me | solution 1 for DepthDecay.run_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:16:13.509338+00:00
-- url     : https://prove2.me/submissions/13f600c4-5dc4-47cc-bc16-c8a77df67379

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



/-- More generally, an admissible state never has `m` an odd multiple `(2j+3)n`
of `n`.  This is what keeps the descent away from every branch boundary. -/
theorem ne_odd_mul {s : ℕ × ℕ} (h : Adm s) (j : ℕ) : s.1 ≠ (2 * j + 3) * s.2 := by
  intro hEq
  obtain ⟨hp, _, hg, hpar⟩ := h
  have hdvd : s.2 ∣ s.1 := ⟨2 * j + 3, by rw [hEq]; ring⟩
  have : Nat.gcd s.1 s.2 = s.2 := Nat.gcd_eq_right hdvd
  have hn : s.2 = 1 := by omega
  rw [hn, mul_one] at hEq
  omega


/-! ### The channel at depth one: the first letter is a magnitude readout -/






/-! ### Depth itself is visible: the leading `C`-run length is one division -/








open DepthDecay in
theorem solution{s : ℕ × ℕ} (h : Adm s) {j : ℕ} (hj : j < (s.1 - s.2) / (2 * s.2)) :
    2 * j * s.2 + 3 * s.2 < s.1 := by
  obtain ⟨hp, hlt, hg, hpar⟩ := h
  have hAdm : Adm s := ⟨hp, hlt, hg, hpar⟩
  have h2p : 0 < 2 * s.2 := by omega
  have hstep : (j + 1) * (2 * s.2) ≤ s.1 - s.2 := (Nat.le_div_iff_mul_le h2p).1 hj
  have hle : (2 * j + 3) * s.2 ≤ s.1 :=
    calc (2 * j + 3) * s.2 = (j + 1) * (2 * s.2) + s.2 := by ring
      _ ≤ (s.1 - s.2) + s.2 := Nat.add_le_add_right hstep _
      _ = s.1 := Nat.sub_add_cancel (le_of_lt hlt)
  have hne : s.1 ≠ (2 * j + 3) * s.2 := ne_odd_mul hAdm j
  have hexp : (2 * j + 3) * s.2 = 2 * j * s.2 + 3 * s.2 := by ring
  omega
