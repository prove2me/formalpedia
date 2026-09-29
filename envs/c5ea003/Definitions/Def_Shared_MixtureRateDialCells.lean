-- Prove2me | Definitions.Def_Shared_MixtureRateDialCells
-- name    : Shared_MixtureRateDialCells
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:02:40.609057+00:00
-- url     : https://prove2.me/theorems/532f5459-4351-4f8c-b915-7963803b046c
-- title:
--   Aether Catalog definitions — Shared_MixtureRateDialCells
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.MixtureRateDialCells`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/MixtureRateDialCells.lean by skeleton subtraction
import Mathlib

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

namespace RateDial

open Finset

/-! ## The 16 divisibility cells -/

/-- The divisibility pattern of `v` with respect to the primes `2, 3, 5, 7`:
one of `16` cells. -/
def cellOf (v : ℤ) : Bool × Bool × Bool × Bool :=
  (decide (2 ∣ v), decide (3 ∣ v), decide (5 ∣ v), decide (7 ∣ v))

/-- The cell of the sieve value `v = j² - N`. -/
def cell (N j : ℤ) : Bool × Bool × Bool × Bool := cellOf (j ^ 2 - N)



/-! ## Window populations are position independent -/

/-- The number of `j` in the window `{a, a+1, …, a+209}` of `210` consecutive
integers whose sieve value lies in cell `c`. -/
def windowCount (N a : ℤ) (c : Bool × Bool × Bool × Bool) : ℕ :=
  ∑ i ∈ Finset.range 210, if cell N (a + i) = c then 1 else 0




/-! ## Bit 0 of the grid is exactly `j`-parity -/


/-! ## The rates themselves are real: quadratic-residue modulation -/




/-! ## A kernel-checked rate table

Real data for `N = 8051 = 83 · 97` (odd, `8051 ≡ 2 mod 3`, a quadratic
non-residue mod `3`).  These are the exact cell populations of a `210`-window;
by `windowCount_const` the very same numbers occur at *every* window position,
which is the content of the flat-composition finding. -/

section RateTable

set_option maxRecDepth 1000000





end RateTable

end RateDial


