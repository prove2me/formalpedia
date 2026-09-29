-- Prove2me | Definitions.Def_Cryptography_DepthDecay_WindowSensor
-- name    : Cryptography_DepthDecay_WindowSensor
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:12:18.302429+00:00
-- url     : https://prove2.me/theorems/d5f1053b-d4f4-446c-9a1c-edef493773cf
-- title:
--   Aether Catalog definitions — Cryptography_DepthDecay_WindowSensor
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.DepthDecay.WindowSensor`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/DepthDecay/WindowSensor.lean by skeleton subtraction
import Mathlib

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

namespace DepthDecay

/-- The three Berggren descent letters. -/
inductive Letter
  | A : Letter
  | B : Letter
  | C : Letter
  deriving DecidableEq, Repr

/-- Admissible pairs: the `(m,n)` coordinates of primitive Pythagorean triples. -/
def Adm (s : ℕ × ℕ) : Prop :=
  0 < s.2 ∧ s.2 < s.1 ∧ Nat.gcd s.1 s.2 = 1 ∧ (s.1 + s.2) % 2 = 1

/-- The root of the Berggren tree, corresponding to the triple `(3,4,5)`. -/
def root : ℕ × ℕ := (2, 1)

/-- Which inverse Berggren branch a state came from: decided by the ratio `m/n`
against the cut points `2` and `3`. -/
def letterOf (s : ℕ × ℕ) : Letter :=
  if s.1 < 2 * s.2 then Letter.A else if s.1 < 3 * s.2 then Letter.B else Letter.C

/-- The descent (parent) map on admissible pairs. -/
def parent (s : ℕ × ℕ) : ℕ × ℕ :=
  if s.1 < 2 * s.2 then (s.2, 2 * s.2 - s.1)
  else if s.1 < 3 * s.2 then (s.2, s.1 - 2 * s.2)
  else (s.1 - 2 * s.2, s.2)

/-- The `k`-th letter of the descent path of `s` (letter `0` is the first step). -/
def letterAt (k : ℕ) (s : ℕ × ℕ) : Letter := letterOf (parent^[k] s)

/-- The `W`-window magnitude sensor: the ratio `m/n` truncated to `W` binary
places. -/
def probe (W : ℕ) (s : ℕ × ℕ) : ℕ := 2 ^ W * s.1 / s.2

/-- Decoding of the first letter from the one-bit probe. -/
def letterFromProbe (p : ℕ) : Letter :=
  if p ≤ 3 then Letter.A else if p ≤ 5 then Letter.B else Letter.C

/-! ### Basic structure of admissible states -/





/-! ### The channel at depth one: the first letter is a magnitude readout -/






/-! ### Depth itself is visible: the leading `C`-run length is one division -/







end DepthDecay


