-- Prove2me | solution 1 for Combinatorics.KneeInvariance.ofCountProfile_agree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:31:20.090874+00:00
-- url     : https://prove2.me/submissions/7b7e78b9-e5b6-40ac-8c56-8cef8ad12876

-- Sol generated from Combinatorics/KneeInvariance.lean
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




/-- The number of `Fin n` indices below a threshold `m ≤ n` is `m`. -/
theorem card_filter_val_lt {n m : ℕ} (hm : m ≤ n) :
    (univ.filter fun i : Fin n => (i : ℕ) < m).card = m := by
  have hcard : (univ.filter fun i : Fin n => (i : ℕ) < m)
      = (Finset.range m).attachFin (fun a ha => lt_of_lt_of_le (mem_range.mp ha) hm) := by
    ext i
    simp [Finset.mem_attachFin]
  rw [hcard, Finset.card_attachFin, Finset.card_range]







/-! ## Invariance: the sweep only sees the demand multiset -/





/-! ## Full decoupling: knee and accuracy are independent coordinates -/








/-! ## Demand domination: the `code < prose` direction -/


/-! ## Shape preservation: the scale increment shifts the knee rigidly -/


/-! ## Corpus mixing -/




/-! ## A Markov bridge: thin demand tails force small budgets -/




/-! ## Realisability: every measured count profile comes from a workload -/


theorem ofCountProfile_demand_le_iff {n : ℕ} {t : ℕ → ℕ} (ht : Monotone t) {j : ℕ}
    (hsat : ∀ i : Fin n, ∃ k, (i : ℕ) < t k) (i : Fin n) (k : ℕ) :
    (ofCountProfile n t j).demand i ≤ k ↔ (i : ℕ) < t k := by
  constructor
  · intro h
    have hmem : (i : ℕ) < t (sInf {k | (i : ℕ) < t k}) :=
      Nat.sInf_mem (by simpa [Set.Nonempty] using hsat i)
    exact lt_of_lt_of_le hmem (ht h)
  · intro h
    exact Nat.sInf_le h

/-- **Realisation theorem.**  Every monotone count profile that is bounded by the
window count and eventually saturates it is the exact agreement profile of an
honest workload — with any prescribed accuracy.  Measured sweeps are therefore
not idealisations: they are attained. -/
theorem ofCountProfile_agreeCount {n : ℕ} {t : ℕ → ℕ} (ht : Monotone t)
    (hle : ∀ k, t k ≤ n) (hsat : ∃ K, t K = n) (j k : ℕ) :
    agreeCount (ofCountProfile n t j) k = t k := by
  have hsat' : ∀ i : Fin n, ∃ k, (i : ℕ) < t k := by
    obtain ⟨K, hK⟩ := hsat
    exact fun i => ⟨K, by rw [hK]; exact i.isLt⟩
  have hset : (univ.filter fun i : Fin n => (ofCountProfile n t j).demand i ≤ k)
      = univ.filter fun i : Fin n => (i : ℕ) < t k := by
    apply filter_congr
    intro i _
    simp [ofCountProfile_demand_le_iff ht hsat' i k]
  unfold agreeCount
  rw [hset, card_filter_val_lt (hle k)]





open Combinatorics.KneeInvariance in
theorem solution{n : ℕ} {t : ℕ → ℕ} (ht : Monotone t)
    (hle : ∀ k, t k ≤ n) (hsat : ∃ K, t K = n) (j k : ℕ) :
    (ofCountProfile n t j).agree k = (t k : ℚ) / n := by
  unfold Workload.agree
  rw [ofCountProfile_agreeCount ht hle hsat]
