-- Prove2me | solution 1 for Cryptography.TernaryReversible.not_injective_at_eight_of_not_exactlyOne
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:10:23.751372+00:00
-- url     : https://prove2.me/submissions/ba9ff813-9709-4dd1-8e35-a10039e3f3e8

-- Sol generated from Cryptography/TernaryReversible/AffineTest.lean
import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_Additive
import Definitions.Def_Cryptography_TernaryReversible_Core
import Definitions.Def_Cryptography_TernaryReversible_General
import Theorems.Thm_Cryptography_TernaryReversible_kernelInj1
import Theorems.Thm_Cryptography_TernaryReversible_kernelInj2
import Theorems.Thm_Cryptography_TernaryReversible_kernelInj4
import Theorems.Thm_Cryptography_TernaryReversible_kernelInj8a
import Theorems.Thm_Cryptography_TernaryReversible_kernelInj8b
import Theorems.Thm_Cryptography_TernaryReversible_not_injective_globalMapA_of_dvd

/-!
# A single cycle length decides reversibility of affine ternary rules

`Additive.lean` shows that an affine rule `addRule α β γ δ` is bijective on every finite
cycle iff exactly one of `α, β, γ` is nonzero, the obstruction in the remaining cases being
a kernel vector living on a cycle of length `1`, `2`, `4` or `8` (the orders of the roots
of unity available in `𝔽₉ˣ`).

Combining this with the divisor monotonicity of `Periodicity.lean` — injectivity at length
`n` implies injectivity at every divisor of `n` — all four bad lengths can be *pulled up
into the single length* `8`, because `1, 2, 4, 8` all divide `8`.  The infinite test
"bijective on every cycle" therefore collapses, inside the affine class, to **one finite
test on the `8`-cycle**, i.e. to injectivity of a single map on `3⁸ = 6561` states.

## Main results

* `not_injective_at_eight_of_not_exactlyOne` — every affine obstruction is visible at
  length `8`;
* `addRule_cycleBijective_iff_injective_at_eight` — the one-length criterion;
* `addRule_bad_lengths_multiples_of_eight` — a non-reversible affine rule fails on *every*
  multiple of `8`, hence on infinitely many cycle lengths.
-/

open Cryptography
open TernaryReversible

/-- The ternary global map is the general one, specialised to `Alph`. -/
theorem globalMap_eq_globalMapA (g : LocalRule) (n : ℕ) :
    globalMap (n := n) g = globalMapA (n := n) g := rfl





open Cryptography.TernaryReversible in
theorem solution{α β γ δ : Alph}
    (h : ¬ ExactlyOneNonzero α β γ) :
    ¬ Function.Injective (globalMap (n := 8) (addRule α β γ δ)) := by
  have lift : ∀ m : ℕ, m ∣ 8 → ¬ Function.Injective (globalMap (n := m) (addRule α β γ δ)) →
      ¬ Function.Injective (globalMap (n := 8) (addRule α β γ δ)) := by
    intro m hm hmm
    rw [globalMap_eq_globalMapA]
    rw [globalMap_eq_globalMapA] at hmm
    exact not_injective_globalMapA_of_dvd hm hmm
  have hcases : ∀ x : Alph, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases hcases α with rfl | rfl | rfl <;> rcases hcases β with rfl | rfl | rfl <;>
    rcases hcases γ with rfl | rfl | rfl <;>
    first
      | exact absurd (show ExactlyOneNonzero _ _ _ by decide) h
      | exact lift 1 (by norm_num) (kernelInj1 (by decide))
      | exact lift 2 (by norm_num) (kernelInj2 (by decide))
      | exact lift 4 (by norm_num) (kernelInj4 (by decide))
      | exact kernelInj8a (by decide)
      | exact kernelInj8b (by decide)
