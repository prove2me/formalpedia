-- Prove2me | Theorems.Thm_CRTSplitNoGo_successor_firstClosureTime
-- name    : CRTSplitNoGo.successor_firstClosureTime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T06:49:35.783337+00:00
-- url     : https://prove2.me/theorems/2e24bad2-57f4-4c1d-bfb9-51afcf8db104
-- title:
--   Extreme case (regime (c)).
-- statement:
--   **Extreme case (regime (c)).**  For the successor map the first closure time is exactly the
--   modulus: `m` steps, the worst possible value allowed by the pigeonhole bound.  For a semiprime
--   `N = p q` this is `min p q ≈ √N`: maximally far from `poly(log N)`.
--
--   ```lean
--   theorem CRTSplitNoGo.successor_firstClosureTime(m : ℕ) [NeZero m] (x0 : ℤ) :
--       firstClosureTime (X + 1) m x0 = m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/CRTSplitNoGoClosureTime.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/CRTSplitNoGoClosureTime.lean#L136

-- Thm stub generated from Bridges/CRTSplitNoGoClosureTime.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGoClosureTime

/-!
# The CRT-Split No-Go, Part IV: the reveal time *is* the first one-sided closure time

Parts I–III established that a reveal is an exclusive cycle closure of the reduced dynamics.
Here we turn that into an exact identity for the *time* at which an `N`-explicit iteration can
first exhibit a factor.

For an integer polynomial `f`, a seed `x₀` and a modulus `m`, let `firstClosureTime f m x₀` be
the least `t` for which the reduced orbit revisits an earlier value.  Then:

* `firstClosureTime_le`: it is at most `m` (pigeonhole) — the only unconditional bound;
* `no_reveal_before_min_closure`: nothing is revealed before
  `min (firstClosureTime f p x₀) (firstClosureTime f q x₀)`;
* `reveal_at_min_closure`: as soon as the two closure times differ, a factor *is* revealed at
  that minimum.

Hence for `N`-explicit iterations the reveal time equals `min(T_p, T_q)` (whenever the two
differ), a quantity determined entirely by the reduced dynamics mod `p` and mod `q`.  Both
ends of the range are realised:

* generic nonlinear maps sit at the birthday scale `T_p ≈ √p` (verified CTST demo, Part III);
* the structurally simple successor map sits at the extreme `T_p = p` exactly
  (`successor_firstClosureTime`).

In neither case — nor anywhere in between — is `min(T_p, T_q)` polynomial in `log N`, since it
is bounded below by the corresponding orbit statistics of a modulus of size `≈ √N`.
-/

open CRTSplitNoGo

open Polynomial
open scoped Classical










/-! ## The two extremes of the closure time -/

theorem CRTSplitNoGo.successor_firstClosureTime(m : ℕ) [NeZero m] (x0 : ℤ) :
    firstClosureTime (X + 1) m x0 = m := by sorry
