-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RenewalCore
-- name    : AnalyticCombinatorics_Ch8_Partitions_RenewalCore
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:04:49.4141+00:00
-- url     : https://prove2.me/theorems/4afdeed8-33c4-4f97-937f-0df797b45b4f
-- title:
--   Renewal Core
-- statement:
--   The source-linked mathematical setting supplies the finite-kernel, rank, moment, renewal or sequence models used by the exact support contracts in this group. The literal model declarations, where catalogued below, retain their source parameters and assumptions. Definition prose must be refined against the actual complete compiler-derived owner before an upload payload is prepared.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/RenewalCore.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# TASK T2.2 core: discrete renewal machinery for the rank-band overshoot/overlap brick

Mathlib has no renewal theory, so we build it from scratch in the repo's deterministic
finite-sum style.  This file sets up the increment-law convolution apparatus and the elementary
facts that do *not* require the renewal limit:

* `IsIncrementLaw p` — `p` is a probability mass supported on `{1,2,…}` (no atom at `0`);
* `convPow p j` — the law of the sum of `j` i.i.d. increments (`j`-fold convolution), with
  `convPow p 0 = δ₀`, `convPow p (j+1) = convPow p j ⋆ p`;
* `renewalMass p N k = ∑_{j<N} convPow p j k` — the truncated expected number of visits to
  level `k` using at most `N` renewals;
* nonnegativity, the total-mass identity `∑_k convPow p j k = 1`, the support fact
  `convPow p j k = 0` for `k < j` (each of the `j` increments is `≥ 1`), and the
  **increment exponential tail ⟹ convolution tail** estimate used by the offset-tail bound.

The genuinely hard renewal-limit / coupling facts live in `RenewalOverlap.lean`.

Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Renewal

/-- An **increment law**: a probability mass on `ℕ` with no atom at `0` (the renewal increments
are all `≥ 1`).  A `tsum`-free total mass over `Finset.range` is awkward because the support
is infinite; we instead require summability and `∑' = 1`. -/
structure IsIncrementLaw (p : ℕ → ℝ) : Prop where
  nonneg : ∀ d, 0 ≤ p d
  zero : p 0 = 0
  summable : Summable p
  total : ∑' d, p d = 1

/-- Convolution of two nonnegative summable masses, `(p ⋆ q) k = ∑_{i+j=k} p i q j`, written as the
finite antidiagonal sum (only finitely many terms are nonzero for fixed `k`). -/
noncomputable def conv (p q : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ ij ∈ Finset.antidiagonal k, p ij.1 * q ij.2

/-- `j`-fold convolution power: `convPow p 0 = δ₀`, `convPow p (j+1) = convPow p j ⋆ p`. -/
noncomputable def convPow (p : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun k => if k = 0 then 1 else 0
  | (j+1) => fun k => conv (convPow p j) p k

@[simp] lemma convPow_zero (p : ℕ → ℝ) (k : ℕ) :
    convPow p 0 k = if k = 0 then 1 else 0 := rfl

/-! ## Nonnegativity -/

/-! ## Support: `convPow p j` is supported on `{k ≥ j}` (each increment is `≥ 1`). -/

/-! ## Total mass: `∑'_k convPow p j k = 1`. -/


end AnalyticCombinatorics.Ch8.Partitions.Renewal


