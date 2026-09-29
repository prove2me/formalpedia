-- Prove2me | Definitions.Def_Probability_WignerEvenWalkCount
-- name    : Probability_WignerEvenWalkCount
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:46:46.578508+00:00
-- url     : https://prove2.me/theorems/054f8622-74ad-4345-b26b-dc5e623db762
-- title:
--   Aether Catalog definitions — Probability_WignerEvenWalkCount
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.WignerEvenWalkCount`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/WignerEvenWalkCount.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_WignerAllOrderParity
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Kernel-verified even-walk counts, and exact small-dimension trace moments

`Probability.WignerAllOrderParity` reduces every trace moment of the symmetric
Rademacher ensemble to a *count*:

`E [tr (W^(m+1))] = #{ closed (m+1)-walks that are loop-free with all edge
multiplicities even }`.

Because `RademacherWigner.IsEvenWalk` is decidable, this count is a finite,
kernel-checkable quantity.  This file records the packaged counting form
(`expect_trace_pow_eq_card`) together with several exact values obtained by
`decide` — a genuine verification of the numerical evidence of
`ComputationalEvidence.md` inside the kernel, rather than by an external
computation:

* `N = 3, m = 4`: `18` even closed walks, so `E [tr W⁴] = 18`, matching
  `2N(N-1)² - N(N-1) = 18`;
* `N = 4, m = 4`: `60`, matching `2·4·9 - 12 = 60`;
* `N = 2, m = 6`: `2`, and `N = 3, m = 6`: `66`, matching the conjectural sixth
  moment `N(N-1)(5N² - 15N + 11)` of `FUTURE_DIRECTIONS.md` (`2` and `66`);
* `N = 3, m = 3` and `N = 3, m = 5`: `0`, an independent kernel check of the
  odd-order vanishing theorem `expect_trace_pow_odd`.
-/

open Matrix BigOperators Finset

namespace RademacherWigner

variable {N : ℕ}

/-- The set of even closed `(m+1)`-walks, as a `Finset` of pairs
(starting vertex, intermediate vertices). -/
def evenWalks (N m : ℕ) : Finset (Fin N × (Fin m → Fin N)) :=
  (univ : Finset (Fin N × (Fin m → Fin N))).filter fun x => IsEvenWalk m x.1 x.2


/-! ### Kernel-verified counts -/







/-! ### The resulting exact moments -/






end RademacherWigner


