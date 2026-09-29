-- Prove2me | Theorems.Thm_RateDial_two_dvd_iff_odd
-- name    : RateDial.two_dvd_iff_odd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:50:09.211199+00:00
-- url     : https://prove2.me/theorems/d5fbe45b-3c13-4e83-8ddd-ae5850b42835
-- title:
--   For odd `N`, `2 â£ jÂ² - N` holds precisely when `j` is odd: the parity
-- statement:
--   For odd `N`, `2 â£ jÂ² - N` holds precisely when `j` is odd: the parity
--   "carrier" is a coordinate of the divisibility grid, not something outside it.
--
--   ```lean
--   theorem RateDial.two_dvd_iff_odd{N : ℤ} (hN : Odd N) (j : ℤ) :
--       (2 : ℤ) ∣ j ^ 2 - N ↔ Odd j := by sorry
--   /-! ## The rates themselves are real: quadratic-residue modulation -/
--
--
--
--
--   /-! ## A kernel-checked rate table
--
--   Real data for `N = 8051 = 83 · 97` (odd, `8051 ≡ 2 mod 3`, a quadratic
--   non-residue mod `3`).  These are the exact cell populations of a `210`-window;
--   by `windowCount_const` the very same numbers occur at *every* window position,
--   which is the content of the flat-composition finding. -/
--
--
--   set_option maxRecDepth 1000000
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/MixtureRateDialCells.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/MixtureRateDialCells.lean#L115

-- Thm stub generated from Shared/MixtureRateDialCells.lean
import Mathlib
import Definitions.Def_Shared_MixtureRateDialCells

/-!
# The divisibility grid of `j² - N` is a rate dial, not a position dial (Part I)

Context: experiment 588c / paper 242.  A mid-window excess in the small-prime
sieve hit profile was tested against a **16-cell divisibility mixture baseline**:
each sieve value `v = j² - N` is labelled by its divisibility pattern
`(2 ∣ v, 3 ∣ v, 5 ∣ v, 7 ∣ v)`, giving `16` cells, and the baseline prediction is
`PRED(t) = Σ_c κ_c · S_c(t)` with per-cell rates `κ_c` fitted on the flanks.

The measurement found the class *composition* flat in the window coordinate
(max cell drift `0.269 %`), so the mixture had no positional freedom.  This file
proves the structural reason: **the cell label of `j² - N` is a periodic
function of `j` with period `210 = 2·3·5·7`, hence every window of `210`
consecutive `j` contains exactly the same number of members of every cell.**
Composition is therefore *exactly* position-independent, whatever `N` is.

Main results.

* `cellOf_periodic`, `cell_periodic` — the cell label is `210`-periodic.
* `windowCount_succ`, `windowCount_const` — the per-cell population of a window
  of `210` consecutive `j` does not depend on where the window starts.
* `two_dvd_iff_odd` — for odd `N`, bit `0` of the grid (`2 ∣ j² - N`) is exactly
  the parity of `j`: parity is *inside* the grid, not an extra carrier.
* `windowCount_8051_table`, `windowCount_8051_three_empty`,
  `windowCount_8051_parity_split`, `windowCount_8051_table_everywhere` — a
  kernel-checked rate table for `N = 8051 = 83·97`, and the same table at every
  window position.
* `sqCount_three`, `sqCount_five`, `sqCount_seven` — the per-prime rates are
  genuinely modulated (`0`, `1` or `2` roots mod `p`, i.e. rate `0`, `1/p` or
  `2/p`), so the "rate dial" really does turn; `windowCount_const` says it never
  turns *with position*.
-/

set_option maxRecDepth 8000

open RateDial

open Finset

/-! ## The 16 divisibility cells -/





/-! ## Window populations are position independent -/





/-! ## Bit 0 of the grid is exactly `j`-parity -/

theorem RateDial.two_dvd_iff_odd{N : ℤ} (hN : Odd N) (j : ℤ) :
    (2 : ℤ) ∣ j ^ 2 - N ↔ Odd j := by sorry
