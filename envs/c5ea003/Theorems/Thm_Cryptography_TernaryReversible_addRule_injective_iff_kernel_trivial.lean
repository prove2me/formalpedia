-- Prove2me | Theorems.Thm_Cryptography_TernaryReversible_addRule_injective_iff_kernel_trivial
-- name    : Cryptography.TernaryReversible.addRule_injective_iff_kernel_trivial
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:44:53.616236+00:00
-- url     : https://prove2.me/theorems/f8e74307-9946-4f22-b053-a8bb2b47761f
-- title:
--   For an affine rule, injectivity of the global map on the cycle of length `n` is exactly
-- statement:
--   For an affine rule, injectivity of the global map on the cycle of length `n` is exactly
--   triviality of the kernel of its linear part on that cycle.
--
--   ```lean
--   theorem Cryptography.TernaryReversible.addRule_injective_iff_kernel_trivial(α β γ δ : Alph) (n : ℕ) :
--       Function.Injective (globalMap (n := n) (addRule α β γ δ)) ↔
--         ∀ s : ZMod n → Alph, (∀ i : ZMod n, α * s (i - 1) + β * s i + γ * s (i + 1) = 0) →
--           s = fun _ => 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/TernaryReversible/AffineTightness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/TernaryReversible/AffineTightness.lean#L32

-- Thm stub generated from Cryptography/TernaryReversible/AffineTightness.lean
import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_Additive
import Definitions.Def_Cryptography_TernaryReversible_Core

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

theorem Cryptography.TernaryReversible.addRule_injective_iff_kernel_trivial(α β γ δ : Alph) (n : ℕ) :
    Function.Injective (globalMap (n := n) (addRule α β γ δ)) ↔
      ∀ s : ZMod n → Alph, (∀ i : ZMod n, α * s (i - 1) + β * s i + γ * s (i + 1) = 0) →
        s = fun _ => 0 := by sorry
