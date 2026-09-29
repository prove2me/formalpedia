-- Prove2me | solution 1 for DepthDecay.letterAt_eq_of_probe_one_of_prefix_C
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:22:35.149837+00:00
-- url     : https://prove2.me/submissions/899c9bda-7021-407d-8c25-7f90f85c3934

-- Sol generated from Cryptography/DepthDecay/WindowSensor.lean
import Mathlib
import Definitions.Def_Cryptography_DepthDecay_WindowSensor
import Theorems.Thm_DepthDecay_Adm_parent
import Theorems.Thm_DepthDecay_letterAt_succ
import Theorems.Thm_DepthDecay_letterOf_eq_of_probe_one

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





/-! ### The channel at depth one: the first letter is a magnitude readout -/



/-- A `C`-step shifts the one-bit probe down by exactly `4`. -/
theorem probe_one_parent_of_C {s : ℕ × ℕ} (h : Adm s) (hC : letterOf s = Letter.C) :
    probe 1 (parent s) + 4 = probe 1 s := by
  have hp := h.1
  have hA : ¬ s.1 < 2 * s.2 := by
    intro hA; rw [letterOf, if_pos hA] at hC; exact Letter.noConfusion hC
  have hB : ¬ s.1 < 3 * s.2 := by
    intro hB; rw [letterOf, if_neg hA, if_pos hB] at hC; exact Letter.noConfusion hC
  have hpar : parent s = (s.1 - 2 * s.2, s.2) := by simp [parent, hA, hB]
  have hsplit : 2 * s.1 = 2 * (s.1 - 2 * s.2) + 4 * s.2 := by omega
  simp only [probe, pow_one, hpar, hsplit]
  rw [show 2 * (s.1 - 2 * s.2) + 4 * s.2 = 2 * (s.1 - 2 * s.2) + s.2 * 4 by ring,
    Nat.add_mul_div_left _ _ hp]



/-! ### Depth itself is visible: the leading `C`-run length is one division -/








open DepthDecay in
theorem solution:
    ∀ (k : ℕ) {s s' : ℕ × ℕ}, Adm s → Adm s' → probe 1 s = probe 1 s' →
      (∀ j < k, letterAt j s = Letter.C) → letterAt k s = letterAt k s' := by
  intro k
  induction k with
  | zero =>
    intro s s' h h' hp _
    simpa [letterAt] using letterOf_eq_of_probe_one h h' hp
  | succ k ih =>
    intro s s' h h' hp hC
    have hC0 : letterOf s = Letter.C := by simpa [letterAt] using hC 0 (Nat.succ_pos k)
    have hC0' : letterOf s' = Letter.C := by
      rw [← letterOf_eq_of_probe_one h h' hp]; exact hC0
    have hroot : ∀ t : ℕ × ℕ, Adm t → letterOf t = Letter.C → t ≠ root := by
      intro t _ hCt hEq
      rw [hEq] at hCt
      simp [letterOf, root] at hCt
    have hpp : probe 1 (parent s) = probe 1 (parent s') := by
      have e1 := probe_one_parent_of_C h hC0
      have e2 := probe_one_parent_of_C h' hC0'
      omega
    have hprefix : ∀ j < k, letterAt j (parent s) = Letter.C := by
      intro j hj
      have := hC (j + 1) (by omega)
      rwa [letterAt_succ] at this
    have := ih (h.parent (hroot s h hC0)) (h'.parent (hroot s' h' hC0')) hpp hprefix
    rw [letterAt_succ, letterAt_succ]
    exact this
