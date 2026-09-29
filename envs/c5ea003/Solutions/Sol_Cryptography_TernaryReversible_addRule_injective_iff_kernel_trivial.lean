-- Prove2me | solution 1 for Cryptography.TernaryReversible.addRule_injective_iff_kernel_trivial
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:03:13.527588+00:00
-- url     : https://prove2.me/submissions/8abf746c-bdb4-4b27-9dac-cdd3cf4d8d18

-- Sol generated from Cryptography/TernaryReversible/AffineTightness.lean
import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_Additive
import Definitions.Def_Cryptography_TernaryReversible_Core
import Theorems.Thm_Cryptography_TernaryReversible_not_injective_of_kernel

/-!
# The length-`8` test for affine rules is sharp

`AffineTest.lean` reduces cycle-bijectivity of an affine ternary rule to injectivity on the
single cycle of length `8`.  Here we show that this length cannot be lowered: the affine
rule

`addRule 1 1 2 0 : a b c ↦ a + b + 2c`

is injective on **every** cycle of length `1, 2, 3, 4, 5, 6, 7` and yet fails at length `8`,
so no test using only cycles of length `≤ 7` can decide reversibility, even inside the
affine class.

The mechanism is arithmetic in `𝔽₉`: the characteristic polynomial `2x² + x + 1` of the
recurrence has roots of multiplicative order `8` in `𝔽₉ˣ` (a cyclic group of order `8`), so
the first cycle length carrying a nonzero kernel vector is exactly `8`.

## Main results

* `addRule_injective_iff_kernel_trivial` — for affine rules injectivity on a cycle is
  triviality of the kernel of the linear part;
* `affine_eight_test_sharp` — `addRule 1 1 2 0` is injective on all cycles of length
  `≤ 7` but is not cycle-bijective.
-/

open Cryptography
open TernaryReversible

set_option maxRecDepth 4000


/-! ### The kernel of `a + b + 2c` is trivial on every cycle of length at most `7` -/










open Cryptography.TernaryReversible in
theorem solution(α β γ δ : Alph) (n : ℕ) :
    Function.Injective (globalMap (n := n) (addRule α β γ δ)) ↔
      ∀ s : ZMod n → Alph, (∀ i : ZMod n, α * s (i - 1) + β * s i + γ * s (i + 1) = 0) →
        s = fun _ => 0 := by
  constructor
  · intro hinj s hker
    by_contra hs
    exact not_injective_of_kernel s hs hker hinj
  · intro hker s t hst
    have hzero : (fun i => s i - t i) = fun _ => (0 : Alph) := by
      refine hker _ ?_
      intro i
      have h := congrFun hst i
      have h' : α * s (i - 1) + β * s i + γ * s (i + 1) + δ
          = α * t (i - 1) + β * t i + γ * t (i + 1) + δ := h
      have : α * (s (i - 1) - t (i - 1)) + β * (s i - t i) + γ * (s (i + 1) - t (i + 1))
          = (α * s (i - 1) + β * s i + γ * s (i + 1) + δ)
            - (α * t (i - 1) + β * t i + γ * t (i + 1) + δ) := by ring
      rw [this, h']
      ring
    funext i
    have := congrFun hzero i
    exact sub_eq_zero.1 this
