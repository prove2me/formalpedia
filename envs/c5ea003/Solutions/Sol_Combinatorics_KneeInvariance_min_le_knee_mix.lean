-- Prove2me | solution 1 for Combinatorics.KneeInvariance.min_le_knee_mix
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:31:18.869386+00:00
-- url     : https://prove2.me/submissions/cf1f99ff-c950-41e1-896f-8df2b8c29923

-- Sol generated from Combinatorics/KneeInvariance.lean
import Mathlib
import Definitions.Def_Combinatorics_KneeInvariance
import Theorems.Thm_Combinatorics_KneeInvariance_knee_le
import Theorems.Thm_Combinatorics_KneeInvariance_knee_mem

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




theorem lt_knee_imp {A : ℕ → ℚ} {g : ℚ} {k : ℕ} (h : k < knee A g) : A k < g := by
  by_contra hc
  exact absurd (knee_le (not_lt.mp hc)) (not_le.mpr h)






/-! ## Workloads: demand profiles with correctness bits -/


variable {n : ℕ}











/-! ## Invariance: the sweep only sees the demand multiset -/





/-! ## Full decoupling: knee and accuracy are independent coordinates -/








/-! ## Demand domination: the `code < prose` direction -/


/-! ## Shape preservation: the scale increment shifts the knee rigidly -/


/-! ## Corpus mixing -/




/-! ## A Markov bridge: thin demand tails force small budgets -/




/-! ## Realisability: every measured count profile comes from a workload -/








open Combinatorics.KneeInvariance in
theorem solution{A B : ℕ → ℚ} {θ g : ℚ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hne : ∃ m, g ≤ mixCurve θ A B m) :
    min (knee A g) (knee B g) ≤ knee (mixCurve θ A B) g := by
  set k := knee (mixCurve θ A B) g with hk
  have hmix : g ≤ θ * A k + (1 - θ) * B k := knee_mem hne
  by_contra hc
  push_neg at hc
  have hA : A k < g := lt_knee_imp (lt_of_lt_of_le hc (min_le_left _ _))
  have hB : B k < g := lt_knee_imp (lt_of_lt_of_le hc (min_le_right _ _))
  rcases eq_or_lt_of_le hθ0 with hθ | hθ
  · rw [← hθ] at hmix
    simp only [zero_mul, sub_zero, one_mul, zero_add] at hmix
    linarith
  · have h1 : θ * A k < θ * g := by nlinarith
    have h2 : (1 - θ) * B k ≤ (1 - θ) * g := by nlinarith
    nlinarith
