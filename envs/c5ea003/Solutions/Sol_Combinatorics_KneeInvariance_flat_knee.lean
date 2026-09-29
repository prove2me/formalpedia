-- Prove2me | solution 1 for Combinatorics.KneeInvariance.flat_knee
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:29:28.230839+00:00
-- url     : https://prove2.me/submissions/cc1342e2-9c8e-4348-b7d0-886e9db7730f

-- Sol generated from Combinatorics/KneeInvariance.lean
import Mathlib
import Definitions.Def_Combinatorics_KneeInvariance
import Theorems.Thm_Combinatorics_KneeInvariance_flat_agree_of_ge
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








/-- Characterisation used for the concrete tables: a witness above the gate
together with sub-gate values everywhere below pins the knee exactly. -/
theorem knee_eq_of {A : ℕ → ℚ} {g : ℚ} {k : ℕ} (hk : g ≤ A k)
    (hlt : ∀ j < k, A j < g) : knee A g = k := by
  refine le_antisymm (knee_le hk) ?_
  by_contra hc
  exact absurd (knee_mem ⟨k, hk⟩) (not_le.mpr (hlt _ (not_le.mp hc)))


/-! ## Workloads: demand profiles with correctness bits -/


variable {n : ℕ}











/-! ## Invariance: the sweep only sees the demand multiset -/





/-! ## Full decoupling: knee and accuracy are independent coordinates -/


theorem flat_agree_of_lt {n k j : ℕ} {b : ℕ} (h : b < k) : (flat n k j).agree b = 0 := by
  have : (univ.filter fun i : Fin n => (flat n k j).demand i ≤ b) = ∅ := by
    apply filter_false_of_mem
    intro i _
    exact not_le.mpr h
  unfold Workload.agree agreeCount
  rw [this]
  simp






/-! ## Demand domination: the `code < prose` direction -/


/-! ## Shape preservation: the scale increment shifts the knee rigidly -/


/-! ## Corpus mixing -/




/-! ## A Markov bridge: thin demand tails force small budgets -/




/-! ## Realisability: every measured count profile comes from a workload -/








open Combinatorics.KneeInvariance in
theorem solution{n k j : ℕ} (hn : 0 < n) {g : ℚ} (hg0 : 0 < g) (hg1 : g ≤ 1) :
    knee (flat n k j).agree g = k :=
  knee_eq_of (by rw [flat_agree_of_ge hn (le_refl k)]; exact hg1)
    (fun b hb => by rw [flat_agree_of_lt hb]; exact hg0)
