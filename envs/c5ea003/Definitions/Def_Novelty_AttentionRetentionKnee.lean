-- Prove2me | Definitions.Def_Novelty_AttentionRetentionKnee
-- name    : Novelty_AttentionRetentionKnee
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:05:01.703817+00:00
-- url     : https://prove2.me/theorems/a8776e8b-1779-48d1-8895-309dcc71a1dc
-- title:
--   Aether Catalog definitions — Novelty_AttentionRetentionKnee
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.AttentionRetentionKnee`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/AttentionRetentionKnee.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_AttentionBudgetIncrement

/-!
# Where does an additive key-increment come from? (NET-67, structural layer)

`Novelty.AttentionBudgetIncrement` fixes the two *measured* budget laws of
NET-67 and audits the verdict at the level of arithmetic.  This file asks the
structural question behind the measurement:

> which attention-weight profiles can produce a knee that grows by a **fixed
> number of keys per context doubling**?

We work with the *retention curve* of a sorted attention profile
`p : ℕ → ℝ` — `retained p k = ∑_{i<k} p i` — and its **knee**
`knee p τ = sInf {k | τ ≤ retained p k}`, the smallest number of retained keys
whose mass reaches the drift-assert threshold `τ`.  Section 1 develops the
general theory (monotonicity, the defining inequalities, monotonicity in `τ`
and in the profile).

Section 2 computes everything for the truncated geometric profile
`geoW r n i = (1-r) rⁱ / (1 - rⁿ)` on a context of `n` keys, and proves the
main negative result:

* `knee_geoW_le` / `knee_geoW_bounded` — for a **fixed** decay rate `r` the knee
  is bounded by `⌈log(1-τ)/log r⌉`, *uniformly in the context length* `n`;
* `knee_geoW_eventually_constant` — hence, along contexts `n = 2^j`, the knee is
  monotone and bounded, so its increments are Filter.eventually `0`;
* `no_fixed_geometric_profile_matches_kneeSmall` — consequently **no** fixed
  geometric attention profile can reproduce the measured `+4`-keys-per-doubling
  law of the 0.5B model.  A persistent positive increment is not a property of
  a distribution; it is a property of a *family* of distributions whose decay
  rate degrades with context;
* `knee_truncNorm_bounded` / `no_fixed_profile_matches_kneeSmall` — and the
  obstruction is not the geometric ansatz but summability: **no** fixed profile,
  renormalised to the context, has a context-dependent knee.

Section 3 supplies the family that does work.  With `λ` the decay rate, the
exact key requirement for a tail budget `δ` is `kneeCts λ δ = log(1/δ)/λ`
(`exp_tail_le_iff` — this is a genuine equivalence, not a heuristic).  Then:

* `kneeCts_lamAt` — if the rate degrades as `λ_j = λ₀/(j+1)` over `j` context
  doublings, the knee is exactly affine in `j` with slope `log(1/δ)/λ₀`;
* `scale_halves_increment` — doubling `λ₀` (a *more peaked* model at every
  context) halves the increment.  This is the NET-67 verdict, derived;
* `rate_of_increment` — the converse: an affine knee law with slope `s` *forces*
  `λ_j = (log(1/δ)/s)/(j+1)`.  So "additive keys per doubling" and
  "decay rate ∝ 1/log(context)" are the same statement;
* `calibration_small`, `calibration_large`, `calibration_ratio` — the measured
  pair `(+4, +2)` is realised by `λ₀ = 1` and `λ₀ = 2` at tail budget
  `δ = e⁻⁴`, i.e. *the 1.5B model's attention is exactly twice as peaked*.
-/

namespace Catalog.Novelty.AttentionRetentionKnee

open Finset Catalog.Novelty.AttentionBudgetIncrement

/-! ### 1. Retention curves and their knee -/

/-- Mass retained by the top `k` keys of a *sorted* attention profile `p`
(`p i` is the `i`-th largest attention weight). -/
def retained (p : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ range k, p i




/-- The **knee**: the least number of retained keys whose mass reaches `τ`.
(`sInf ∅ = 0` in `ℕ`; every statement below carries the relevant reachability
hypothesis, so the junk value is never used.) -/
noncomputable def knee (p : ℕ → ℝ) (tau : ℝ) : ℕ := sInf {k | tau ≤ retained p k}






/-! ### 2. A fixed geometric profile has a context-independent knee -/

/-- The truncated geometric attention profile on a context of `n` keys:
`geoW r n i = (1-r) rⁱ / (1-rⁿ)`, a probability vector on `{0,…,n-1}`. -/
noncomputable def geoW (r : ℝ) (n : ℕ) (i : ℕ) : ℝ := (1 - r) * r ^ i / (1 - r ^ n)













/-! ### 2b. The no-go is not about geometric profiles: it holds for *any* fixed one -/


/-- A *fixed* attention profile `p`, renormalised to a context of `n` keys.
This is the general form of `geoW`: the only way a context length can enter a
fixed profile is through the normalising constant. -/
noncomputable def truncNorm (p : ℕ → ℝ) (n : ℕ) (i : ℕ) : ℝ := p i / retained p n




/-! ### 3. The family that does work: a rate degrading like `1 / log(context)` -/

/-- Keys needed to push an exponential attention tail with decay rate `λ` below
the budget `δ`. -/
noncomputable def kneeCts (lam delta : ℝ) : ℝ := Real.log (1 / delta) / lam



/-- Decay rate after `j` context doublings, when the rate degrades inversely
with the log of the context: `λ_j = λ₀ / (j+1)`. -/
noncomputable def lamAt (lam0 : ℝ) (j : ℕ) : ℝ := lam0 / (j + 1)





/-! ### 4. Calibration against the NET-67 measurement -/




end Catalog.Novelty.AttentionRetentionKnee


