-- Prove2me | solution 1 for GeneratorTilt.descCost_lt_ascCost_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:45:11.603647+00:00
-- url     : https://prove2.me/submissions/b46f726d-6849-4128-a7dd-29bb026079e7

-- Sol generated from Novelty/GeneratorTiltWindow.lean
import Mathlib
import Definitions.Def_Novelty_GeneratorTiltWindow
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

open GeneratorTilt

open Finset

/-! ## The two scan costs inside a window -/







/-! ## The canonical window is the balance window -/





/-! ## Pool-level totals -/

variable {ι : Type*}






/-! ## Mean tilt and the exact speedup law -/







/-! ## The tilt-only predictor -/



/-! ## The inversion theorem -/




open GeneratorTilt in
theorem solution(a b d : ℤ) :
    descCost b d < ascCost a d ↔ a + b < 2 * d := by
  unfold ascCost descCost; omega
