-- Prove2me | solution 1 for Catalog.Novelty.AttentionRetentionKnee.geoW_ceil_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:55:11.983423+00:00
-- url     : https://prove2.me/submissions/e81ba7a9-22f6-4db8-ab50-f32ebaaa4a65

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
theorem solution{r tau : ℝ} (h0 : 0 < r) (h1 : r < 1) (htau : tau < 1) :
    r ^ (⌈Real.log (1 - tau) / Real.log r⌉₊) ≤ 1 - tau := by
  set K : ℕ := ⌈Real.log (1 - tau) / Real.log r⌉₊ with hK
  have hlogr : Real.log r < 0 := Real.log_neg h0 h1
  have hslack : (0 : ℝ) < 1 - tau := by linarith
  have hqK : Real.log (1 - tau) / Real.log r ≤ (K : ℝ) := Nat.le_ceil _
  have hmul : (K : ℝ) * Real.log r ≤ (Real.log (1 - tau) / Real.log r) * Real.log r :=
    mul_le_mul_of_nonpos_right hqK hlogr.le
  rw [div_mul_cancel₀ _ (ne_of_lt hlogr)] at hmul
  have hpowpos : (0 : ℝ) < r ^ K := pow_pos h0 K
  have hlogpow : Real.log (r ^ K) = (K : ℝ) * Real.log r := by
    rw [Real.log_pow]
  have hle : Real.log (r ^ K) ≤ Real.log (1 - tau) := by rw [hlogpow]; exact hmul
  exact (Real.log_le_log_iff hpowpos hslack).1 hle
