-- Prove2me | solution 1 for Cryptography.BerggrenModular.valid_leg_lt_hyp2
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T23:54:52.940249+00:00
-- url     : https://prove2.me/submissions/08731c7c-9731-48d4-9ba8-b594f3e35014

-- Sol generated from Cryptography/BerggrenModular/Core.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core

/-!
# Berggren moves over `ℤ`: the exact move classifier and free-monoid seed recovery

This file is the integer-side foundation for the modular study carried out in
`Cryptography.BerggrenModular.Modular` and
`Cryptography.BerggrenModular.Hardness`.

The three Berggren (Barning–Hall) moves `B₁, B₂, B₃` act on integer triples and
preserve the Lorentz form `a² + b² − c²`; on the cone of positive Pythagorean
triples they generate a ternary tree rooted at `(3,4,5)`.

The central object here is an **exact, purely linear classifier**

```
whichMove (a,b,c) = if 5a < 3c then B₁ else if 5a < 4c then B₂ else B₃
```

which reads off, from a single child state, *which* move produced it.  The
thresholds `3/5` and `4/5` are the images of the ratio tests `m < 2n`,
`2n < m < 3n`, `m > 3n` in the Euclid parametrisation `a = m²−n²`, `b = 2mn`,
`c = m²+n²`, transported through `m/n = √((c+a)/(c−a))`.

## Main results

* `whichMove_applyMove` — soundness *and* completeness of the classifier over `ℤ`.
* `applyMove_valid` — the positive Pythagorean cone is invariant.
* `invMove_applyMove` — each move is inverted by an explicit integer matrix.
* `recover_applyWord` — a **linear-time seed-recovery algorithm** over `ℤ`:
  the control word is recovered exactly from a single observed state.
* `applyWord_injective` — the Berggren monoid acts freely on the cone
  (so the length-`k` search space really has `3^k` distinct states).
-/

open Cryptography
open BerggrenModular

/-! ## Moves -/












/-! ## The positive Pythagorean cone -/







/-! ## The exact linear classifier -/




/-! ## Words, orbits and seed recovery -/












/-- The three children of the root, as a sanity check on the classifier. -/
example : applyMove .m1 root = (5, 12, 13) := by norm_num [applyMove, root]

example : applyMove .m2 root = (21, 20, 29) := by norm_num [applyMove, root]

example : applyMove .m3 root = (15, 8, 17) := by norm_num [applyMove, root]

/-! ## Matrix formulation -/






open Cryptography in
theorem solution{v : Tri} (h : Valid v) : v.2.1 < v.2.2 := by
  obtain ⟨ha, hb, hc, hp⟩ := h; nlinarith
