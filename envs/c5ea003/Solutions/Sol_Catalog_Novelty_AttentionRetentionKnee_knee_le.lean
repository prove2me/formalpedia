-- Prove2me | solution 1 for Catalog.Novelty.AttentionRetentionKnee.knee_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:52:34.044534+00:00
-- url     : https://prove2.me/submissions/34c10a31-dc41-43b9-bcad-3488f11f8d72

-- Sol generated from Novelty/AttentionRetentionKnee.lean
import Mathlib
import Definitions.Def_Novelty_AttentionBudgetIncrement
import Definitions.Def_Novelty_AttentionRetentionKnee

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

open Catalog.Novelty.AttentionRetentionKnee

open Finset Catalog.Novelty.AttentionBudgetIncrement

/-! ### 1. Retention curves and their knee -/











/-! ### 2. A fixed geometric profile has a context-independent knee -/














/-! ### 2b. The no-go is not about geometric profiles: it holds for *any* fixed one -/






/-! ### 3. The family that does work: a rate degrading like `1 / log(context)` -/









/-! ### 4. Calibration against the NET-67 measurement -/





open Catalog.Novelty.AttentionRetentionKnee in
theorem solution{p : ℕ → ℝ} {tau : ℝ} {k : ℕ} (hk : tau ≤ retained p k) : knee p tau ≤ k :=
  Nat.sInf_le hk
