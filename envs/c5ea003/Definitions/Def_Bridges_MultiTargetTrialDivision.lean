-- Prove2me | Definitions.Def_Bridges_MultiTargetTrialDivision
-- name    : Bridges_MultiTargetTrialDivision
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:30:12.192224+00:00
-- url     : https://prove2.me/theorems/2854a686-62b2-4116-a83e-e3e23644e5e0
-- title:
--   Aether Catalog definitions — Bridges_MultiTargetTrialDivision
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.MultiTargetTrialDivision`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/MultiTargetTrialDivision.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_TreeSieveLottery

/-!
# The multi-target relaxation is exactly trial division

This file formalises the analysis of the "MULTI-TARGET" relaxation
(round-72 experiment `exp558`).  A tree search whose goal is the *exact* target
`a = N` is relaxed to the much weaker goal `gcd (a, N) > 1`.  Empirically the
relaxation is a `~10^12` speedup over blind FIFO search, but `100 %` of first
hits land at `a = min (p, q)`, with fitted exponent `α = 1.087`, `r² = 1.0`:
dead centre of the trial-division band.  The theorems below explain *why* this
is forced, not accidental.

Main results.

* `firstHit_eq_min` / `isLeast_hit_min` — the least `a ≥ 2` with `gcd (a, N) > 1`
  is **exactly** `min p q` for a semiprime `N = p * q`.  Any search that sweeps
  values in ascending order therefore always first hits at `min p q`; the
  observed histogram is a theorem, not a statistic.
* `min_sq_le` / `ascending_sweep_is_trial_division` — the cost of the ascending
  sweep is `min p q ≤ √N`: exactly the trial-division exponent `1/2`.
* `relaxation_speedup_exact` — relative to the exact target `a = N`, the
  relaxation saves precisely a factor `max p q`, which is between `√N` and
  `N / 2`: a huge but strictly bounded win.
* `rho_beats_trial_division` — the `N^{1/4}` cost of Pollard-ρ beats
  `C · N^{1/2}`-class trial division for every constant `C` once `N > C⁴`;
  so the relaxed search remains dominated.
* `tree_integer_face_trichotomy` — the capstone: any splitter reading a value
  off the integer face of the Berggren tree is in one of three regimes —
  integer square identity (returns `N`, no split), a genuine mod-`N` congruence
  of squares (Dixon/QS class), or an ascending value sweep (trial division,
  cost `min p q`).  Every route ends in a known method.
-/

namespace MultiTarget

open TreeSieve

/-! ## The ascending sweep first-hit theorem -/

/-- The relaxed target predicate: a value `a ≥ 2` is a *hit* for `N` when it
shares a nontrivial factor with `N`. -/
def Hit (N a : ℕ) : Prop := 2 ≤ a ∧ 1 < Nat.gcd a N

instance (N a : ℕ) : Decidable (Hit N a) := by unfold Hit; infer_instance





/-! ## The cost of the sweep is the trial-division exponent -/






/-! ## Pollard-ρ still dominates -/


/-! ## Capstone: every route through the integer face is a known method -/

/-- A splitter reading integers off the tree is in one of three regimes. -/
inductive Regime (N : ℕ) : Type
  /-- The relation is an identity in `ℤ`: `X² = Y²` with `X, Y ≥ 0`. -/
  | integerIdentity (X Y : ℤ) (hX : 0 ≤ X) (hY : 0 ≤ Y) (h : X ^ 2 = Y ^ 2) : Regime N
  /-- The relation is a genuine congruence of squares modulo `N`. -/
  | dixon (x y : ℤ) (hdvd : (N : ℤ) ∣ (x - y) * (x + y))
      (h1 : ¬ (N : ℤ) ∣ (x - y)) (h2 : ¬ (N : ℤ) ∣ (x + y)) : Regime N
  /-- The search sweeps candidate values in ascending order. -/
  | ascendingSweep : Regime N


/-- The outcome that the gcd / sweep step actually produces, read off the
*regime's own data* rather than through a bare existential.  This is what makes
the trichotomy sharp: the disjunct is selected by the constructor, and its
witnesses are the ones the regime supplies. -/
def Regime.Outcome {N : ℕ} : Regime N → Prop
  | .integerIdentity X Y _ _ _ => Int.gcd (X - Y) (N : ℤ) = N
  | .dixon x y _ _ _ => 1 < Int.gcd (x - y) (N : ℤ) ∧ Int.gcd (x - y) (N : ℤ) < N
  | .ascendingSweep => ∃ a : ℕ, IsLeast {b : ℕ | Hit N b} a ∧ a * a ≤ N


end MultiTarget


