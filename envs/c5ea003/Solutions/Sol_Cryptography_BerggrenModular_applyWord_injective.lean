-- Prove2me | solution 1 for Cryptography.BerggrenModular.applyWord_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:17:08.185949+00:00
-- url     : https://prove2.me/submissions/d92f6a13-6d8c-41e2-b340-37fc50bb6917

-- Sol generated from Cryptography/BerggrenModular/Core.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core
import Theorems.Thm_Cryptography_BerggrenModular_applyWord_valid
import Theorems.Thm_Cryptography_BerggrenModular_hyp_le_applyWord
import Theorems.Thm_Cryptography_BerggrenModular_hyp_lt_applyMove
import Theorems.Thm_Cryptography_BerggrenModular_invMove_applyMove
import Theorems.Thm_Cryptography_BerggrenModular_whichMove_applyMove

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











theorem applyMove_injective (i : Move) : Function.Injective (applyMove i) := by
  intro u v h
  have := congrArg (invMove i) h
  rwa [invMove_applyMove, invMove_applyMove] at this

/-! ## The positive Pythagorean cone -/







/-! ## The exact linear classifier -/




/-! ## Words, orbits and seed recovery -/












/-- The three children of the root, as a sanity check on the classifier. -/
example : applyMove .m1 root = (5, 12, 13) := by norm_num [applyMove, root]

example : applyMove .m2 root = (21, 20, 29) := by norm_num [applyMove, root]

example : applyMove .m3 root = (15, 8, 17) := by norm_num [applyMove, root]

/-! ## Matrix formulation -/






@[simp] theorem applyWord_nil (v : Tri) : applyWord [] v = v := rfl

@[simp] theorem applyWord_cons (i : Move) (w : List Move) (v : Tri) :
    applyWord (i :: w) v = applyMove i (applyWord w v) := rfl

open Cryptography in
theorem solution{v : Tri} (h : Valid v) :
    Function.Injective (fun w : List Move => applyWord w v) := by
  intro u
  induction u with
  | nil =>
      intro w hw
      match w with
      | [] => rfl
      | j :: t =>
          exfalso
          have h1 : v.2.2 ≤ (applyWord t v).2.2 := hyp_le_applyWord t h
          have h2 : (applyWord t v).2.2 < (applyMove j (applyWord t v)).2.2 :=
            hyp_lt_applyMove (applyWord_valid t h)
          simp only [applyWord_nil, applyWord_cons] at hw
          rw [← hw] at h2
          linarith
  | cons i s ih =>
      intro w hw
      match w with
      | [] =>
          exfalso
          have h1 : v.2.2 ≤ (applyWord s v).2.2 := hyp_le_applyWord s h
          have h2 : (applyWord s v).2.2 < (applyMove i (applyWord s v)).2.2 :=
            hyp_lt_applyMove (applyWord_valid s h)
          simp only [applyWord_nil, applyWord_cons] at hw
          rw [hw] at h2
          linarith
      | j :: t =>
          simp only [applyWord_cons] at hw
          have hij : i = j := by
            rw [← whichMove_applyMove i (applyWord_valid s h),
              ← whichMove_applyMove j (applyWord_valid t h), hw]
          subst hij
          have : applyWord s v = applyWord t v := applyMove_injective i hw
          exact congrArg (i :: ·) (ih this)
