-- Prove2me | Theorems.Thm_CRTSplitNoGo_reveal_iff_general
-- name    : CRTSplitNoGo.reveal_iff_general
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T06:49:29.026984+00:00
-- url     : https://prove2.me/theorems/207d83db-d464-43a0-b1b3-fefd4ea308b7
-- title:
--   Fact 1, general form.
-- statement:
--   **Fact 1, general form.**  For any `N > 1`, `d` reveals a nontrivial factor of `N` iff some
--   prime factor of `N` divides `d` but `N` does not: the CRT agreement is partial.
--
--   ```lean
--   theorem CRTSplitNoGo.reveal_iff_general{N : ℕ} (hN : 1 < N) (d : ℤ) :
--       RevealsFactor N d ↔ (∃ r : ℕ, r.Prime ∧ r ∣ N ∧ (r : ℤ) ∣ d) ∧ ¬ ((N : ℤ) ∣ d) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/CRTSplitNoGoGeneral.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/CRTSplitNoGoGeneral.lean#L33

-- Thm stub generated from Bridges/CRTSplitNoGoGeneral.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGo
import Definitions.Def_Bridges_CRTSplitNoGoClosureTime

/-!
# The CRT-Split No-Go, Part V: general moduli, barrier 5, and the boundary of the no-go

Three complements to Parts I–IV.

* **General moduli.**  Fact 1 is not special to semiprimes: for any `N > 1`, an integer `d`
  reveals a nontrivial factor of `N` iff some prime factor of `N` divides `d` while `N` itself
  does not (`reveal_iff_general`).  Reveal = *partial* agreement across the CRT decomposition.

* **Barrier 5 (structurally simple maps reveal nothing at all).**  A map that forgets its
  input — a constant polynomial, the paradigmatic "`N`-only" iteration — never reveals a
  factor, at any pair of times `1 ≤ s < t` (`constant_map_no_reveal`).  More generally any map
  whose two reduced orbits close *simultaneously* is blind (`no_reveal_of_simultaneous`).

* **The boundary (adversarial review).**  The no-go is a statement about *regimes*, not a
  universal lower bound: there are `N` for which an `N`-independent iteration reveals a factor
  at an exponent that is reached in `O(log M)` multiplications.  We verify this on the CTST
  modulus itself: `ord_631(2) = 45` divides `45` while `ord_541(2) = 540` does not, so
  `gcd(2^45 - 1, 341371) = 631` (`pollard_pm1_fast_demo`).  Both `630 = 2·3²·5·7` and
  `540 = 2²·3³·5` are smooth, which is exactly regime (b): the cost is the smoothness of the
  orders, an invariant of `p` and `q` that is invisible in `N` — so no *algorithm* can decide
  in advance which regime it is in.  A universal `poly(log N)` lower bound valid for *all*
  `N`-explicit maps would be equivalent to the hardness of factoring and is not claimed here.
-/

open CRTSplitNoGo

open Polynomial

/-! ## Fact 1 for an arbitrary modulus -/

theorem CRTSplitNoGo.reveal_iff_general{N : ℕ} (hN : 1 < N) (d : ℤ) :
    RevealsFactor N d ↔ (∃ r : ℕ, r.Prime ∧ r ∣ N ∧ (r : ℤ) ∣ d) ∧ ¬ ((N : ℤ) ∣ d) := by sorry
