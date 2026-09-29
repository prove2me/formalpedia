-- Prove2me | Theorems.Thm_Combinatorics_KneeInvariance_ofCountProfile_acc
-- name    : Combinatorics.KneeInvariance.ofCountProfile_acc
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:07:40.588522+00:00
-- url     : https://prove2.me/theorems/67018658-20f8-4601-875e-038f469a3926
-- title:
--   OfCountProfile acc
-- statement:
--   Formal statement of `Combinatorics.KneeInvariance.ofCountProfile_acc` from the Aether Catalog (Combinatorics). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Combinatorics.KneeInvariance.ofCountProfile_acc{n : ℕ} (t : ℕ → ℕ) {j : ℕ} (hj : j ≤ n) :
--       (ofCountProfile n t j).acc = (j : ℚ) / n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/KneeInvariance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/KneeInvariance.lean#L459

-- Thm stub generated from Combinatorics/KneeInvariance.lean
import Mathlib
import Definitions.Def_Combinatorics_KneeInvariance

/-!
# Knee invariance: the demand-multiset calculus of budget curves (NET-70)

This file formalises the *combinatorial* content behind the NET-70 measurement
(`MATH-READS-AS-PROSE`):

> A domain jump from English prose to classical mathematical text leaves the
> retention knee `k*` **exactly** where it was (`16` at ctx 512, `20` at ctx
> 1024) even though the full-model accuracy drops by ~12 points
> (`0.4460 → 0.3262` at 512, `0.4612 → 0.3418` at 1024).

The abstraction is the *demand profile*.  A workload is a finite family of
prediction windows; window `i` carries

* a **demand** `r i : ℕ`, the smallest key budget at which the truncated model
  still reproduces the full model's prediction on that window, and
* a **correctness bit** `correct i : Bool`, whether the *full* model's
  prediction on that window is right.

Everything the sweep measures is then read off two derived objects:

* the **agreement curve** `Workload.agree D k = #{i | r i ≤ k} / n`, whose knee
  at a gate `g` is `knee (D.agree) g = sInf {k | g ≤ agree k}`;
* the **accuracy** `Workload.acc D = #{i | correct i} / n`.

The theorems below say, in increasing strength, that these two are *orthogonal
coordinates*:

* `knee_le_iff` — the knee is the left adjoint of the curve (a Galois
  connection); this is the structural reason all later monotonicity facts hold.
* `agree_eq_of_demandMultiset_eq`, `knee_eq_of_demandMultiset_eq` — the entire
  sweep is a function of the **demand multiset** alone: the correctness bits are
  invisible to it.  This is P3 ("knees match despite the accuracy gap") in its
  exact form.
* `decoupling_surjective` — the joint invariant `D ↦ (knee curve, accuracy)` is
  **surjective**: for any target knee `k ≥ 1` and any achievable accuracy value
  there is a workload realising both.  Difficulty and sparsity are therefore
  independent coordinates, not merely uncorrelated in the measured sample.
* `knee_antitone_of_demand_le` — pointwise cheaper demands can only lower the
  knee (the `code < prose` direction of the deployment table).
* `knee_shift` — the **shape-preservation law**: shifting a curve by a scale
  increment `δ` shifts its knee by exactly `δ`, at *every* gate.
* `knee_mix_le_max`, `min_le_knee_mix` — corpus mixing cannot move the knee
  outside the interval spanned by its constituents (barrier (c): "one corpus
  mix").
* `knee_le_of_markov` — a Markov/quantile bridge: the knee is bounded by
  `meanDemand / (1 - gate)`, so a thin demand tail forces a small budget.

None of these mention the accuracy at all — which is the point.
-/

open Combinatorics.KneeInvariance

open Finset

/-! ## The knee of a curve -/










/-! ## Workloads: demand profiles with correctness bits -/


variable {n : ℕ}











/-! ## Invariance: the sweep only sees the demand multiset -/





/-! ## Full decoupling: knee and accuracy are independent coordinates -/








/-! ## Demand domination: the `code < prose` direction -/


/-! ## Shape preservation: the scale increment shifts the knee rigidly -/


/-! ## Corpus mixing -/




/-! ## A Markov bridge: thin demand tails force small budgets -/




/-! ## Realisability: every measured count profile comes from a workload -/

theorem Combinatorics.KneeInvariance.ofCountProfile_acc{n : ℕ} (t : ℕ → ℕ) {j : ℕ} (hj : j ≤ n) :
    (ofCountProfile n t j).acc = (j : ℚ) / n := by sorry
