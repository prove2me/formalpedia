-- Prove2me | Definitions.Def_Bridges_CRTSplitNoGoClosureTime
-- name    : Bridges_CRTSplitNoGoClosureTime
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T06:46:44.1934+00:00
-- url     : https://prove2.me/theorems/ae00c508-3d7c-4fad-9e7c-505b299abf4c
-- title:
--   Aether Catalog definitions — Bridges_CRTSplitNoGoClosureTime
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.CRTSplitNoGoClosureTime`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/CRTSplitNoGoClosureTime.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGo
import Theorems.Thm_CRTSplitNoGo_exists_closure_le

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

namespace CRTSplitNoGo

open Polynomial
open scoped Classical

/-- The reduced orbit revisits, at time `t`, a value it had at some earlier time. -/
def ClosureAt (f : ℤ[X]) (m : ℕ) (x0 : ℤ) (t : ℕ) : Prop :=
  ∃ s, s < t ∧ modOrbit f m x0 t = modOrbit f m x0 s

lemma exists_closureAt (f : ℤ[X]) (m : ℕ) [NeZero m] (x0 : ℤ) : ∃ t, ClosureAt f m x0 t := by
  obtain ⟨s, t, hst, -, h⟩ := exists_closure_le f m x0
  exact ⟨t, s, hst, h⟩

/-- The first time the reduced orbit closes up. -/
noncomputable def firstClosureTime (f : ℤ[X]) (m : ℕ) [NeZero m] (x0 : ℤ) : ℕ :=
  Nat.find (exists_closureAt f m x0)







/-! ## The two extremes of the closure time -/




end CRTSplitNoGo


