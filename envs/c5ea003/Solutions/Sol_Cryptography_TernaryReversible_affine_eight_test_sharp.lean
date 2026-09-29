-- Prove2me | solution 1 for Cryptography.TernaryReversible.affine_eight_test_sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:05:46.941521+00:00
-- url     : https://prove2.me/submissions/f3955c60-bc84-4ade-8f08-1a438294c6ae

-- Sol generated from Cryptography/TernaryReversible/AffineTightness.lean
import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_Additive
import Definitions.Def_Cryptography_TernaryReversible_Core
import Theorems.Thm_Cryptography_TernaryReversible_addRule_injective_iff_kernel_trivial
import Theorems.Thm_Cryptography_TernaryReversible_kernel8a

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

theorem kernel_trivial_112_one :
    ∀ s : ZMod 1 → Alph,
      (∀ i : ZMod 1, (1 : Alph) * s (i - 1) + 1 * s i + 2 * s (i + 1) = 0) → s = fun _ => 0 := by
  decide

theorem kernel_trivial_112_two :
    ∀ s : ZMod 2 → Alph,
      (∀ i : ZMod 2, (1 : Alph) * s (i - 1) + 1 * s i + 2 * s (i + 1) = 0) → s = fun _ => 0 := by
  decide

theorem kernel_trivial_112_three :
    ∀ s : ZMod 3 → Alph,
      (∀ i : ZMod 3, (1 : Alph) * s (i - 1) + 1 * s i + 2 * s (i + 1) = 0) → s = fun _ => 0 := by
  decide

theorem kernel_trivial_112_four :
    ∀ s : ZMod 4 → Alph,
      (∀ i : ZMod 4, (1 : Alph) * s (i - 1) + 1 * s i + 2 * s (i + 1) = 0) → s = fun _ => 0 := by
  decide

theorem kernel_trivial_112_five :
    ∀ s : ZMod 5 → Alph,
      (∀ i : ZMod 5, (1 : Alph) * s (i - 1) + 1 * s i + 2 * s (i + 1) = 0) → s = fun _ => 0 := by
  decide +kernel

theorem kernel_trivial_112_six :
    ∀ s : ZMod 6 → Alph,
      (∀ i : ZMod 6, (1 : Alph) * s (i - 1) + 1 * s i + 2 * s (i + 1) = 0) → s = fun _ => 0 := by
  decide +kernel

theorem kernel_trivial_112_seven :
    ∀ s : ZMod 7 → Alph,
      (∀ i : ZMod 7, (1 : Alph) * s (i - 1) + 1 * s i + 2 * s (i + 1) = 0) → s = fun _ => 0 := by
  decide +kernel



open Cryptography.TernaryReversible in
theorem solution:
    (∀ n : ℕ, 0 < n → n ≤ 7 → Function.Injective (globalMap (n := n) (addRule 1 1 2 0))) ∧
      ¬ CycleBijective (addRule 1 1 2 0) := by
  constructor
  · intro n hn hn7
    interval_cases n
    · exact (addRule_injective_iff_kernel_trivial 1 1 2 0 1).2 kernel_trivial_112_one
    · exact (addRule_injective_iff_kernel_trivial 1 1 2 0 2).2 kernel_trivial_112_two
    · exact (addRule_injective_iff_kernel_trivial 1 1 2 0 3).2 kernel_trivial_112_three
    · exact (addRule_injective_iff_kernel_trivial 1 1 2 0 4).2 kernel_trivial_112_four
    · exact (addRule_injective_iff_kernel_trivial 1 1 2 0 5).2 kernel_trivial_112_five
    · exact (addRule_injective_iff_kernel_trivial 1 1 2 0 6).2 kernel_trivial_112_six
    · exact (addRule_injective_iff_kernel_trivial 1 1 2 0 7).2 kernel_trivial_112_seven
  · exact kernel8a (by decide)
