-- Prove2me | Definitions.Def_Novelty_GeneratorTiltWindow
-- name    : Novelty_GeneratorTiltWindow
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:27:58.440351+00:00
-- url     : https://prove2.me/theorems/2fdf3672-9135-4e3e-8a56-dfb58e8fef01
-- title:
--   Aether Catalog definitions — Novelty_GeneratorTiltWindow
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.GeneratorTiltWindow`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/GeneratorTiltWindow.lean by skeleton subtraction
import Mathlib
/-
# Generator tilt and the window/sqrt scan-order inversion (discrete layer)

This file formalises the *scan-order* cost model behind the "Λ-channel" question for
semiprime factor search, and proves the exact algebraic law that governs which of the two
canonical divisor scan orders wins on a given population of semiprimes.

Setting.  A semiprime `N = p * q` with `p ≤ q` has its small factor `p` in the *canonical
window* `(√(N/2), √N]` exactly when the pair is *balanced*, i.e. `q < 2p`
(`GeneratorTilt.window_iff_balanced`).  Inside a window `[a, b]` one may scan

* **window-ascending**: `a, a+1, …` until the divisor is hit — cost `d - a + 1`;
* **sqrt-descending**:  `b, b-1, …` until the divisor is hit — cost `b - d + 1`.

The two costs are complementary (`ascCost_add_descCost`), so the comparison is decided by a
single scalar: the *tilt* `z = (d - a)/(b - a) ∈ [0,1]`, the normalised height of the divisor
in the window.  The main results are:

* `GeneratorTilt.speedup_eq` — the exact pool speedup
  `S = (L(1 - z̄) + 1)/(L z̄ + 1)` where `z̄` is the mean tilt and `L` the window length;
* `GeneratorTilt.predictor_sub_speedup` / `abs_speedup_sub_predictor_le` — the tilt-only
  predictor `(1 - z̄)/z̄` is exact up to `O(1/L)`, with an explicit error identity;
* `GeneratorTilt.descending_wins_iff_top_heavy` — *the inversion*: sqrt-descending strictly
  beats window-ascending **iff** the pool is top-heavy (`z̄ > 1/2`).  Hence a Λ-style
  window-ascending advantage exists only for bottom-heavy pools; a measured mean tilt
  `z̄ > 1/2` refutes it outright, no matter how the window is realised.

Together with `Novelty.GeneratorTiltRatio` (which computes `z̄` from the prime-ratio law)
this pins down exactly which generator classes can support a window-ascending gain.
-/

namespace GeneratorTilt

open Finset

/-! ## The two scan costs inside a window -/

/-- Touch count of a window-ascending scan of `[a, b]` that stops at divisor `d`. -/
def ascCost (a d : ℤ) : ℤ := d - a + 1

/-- Touch count of a sqrt-descending scan of `[a, b]` that stops at divisor `d`. -/
def descCost (b d : ℤ) : ℤ := b - d + 1





/-! ## The canonical window is the balance window -/





/-! ## Pool-level totals -/

variable {ι : Type*}

/-- Total ascending touch count over a pool. -/
def totalAsc (s : Finset ι) (a : ℤ) (d : ι → ℤ) : ℤ := ∑ i ∈ s, ascCost a (d i)

/-- Total descending touch count over a pool. -/
def totalDesc (s : Finset ι) (b : ℤ) (d : ι → ℤ) : ℤ := ∑ i ∈ s, descCost b (d i)




/-! ## Mean tilt and the exact speedup law -/

/-- The tilt of a divisor: its normalised height in the window, `0` at the bottom,
`1` at the top. -/
noncomputable def tilt (a b : ℤ) (x : ℤ) : ℝ := ((x : ℝ) - a) / ((b : ℝ) - a)

/-- Mean tilt of a pool (`z̄`). -/
noncomputable def meanTilt (s : Finset ι) (a b : ℤ) (d : ι → ℤ) : ℝ :=
  (∑ i ∈ s, tilt a b (d i)) / s.card





/-! ## The tilt-only predictor -/



/-! ## The inversion theorem -/



end GeneratorTilt


