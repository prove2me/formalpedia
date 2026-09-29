-- Prove2me | solution 1 for UniversalRedundancy.sum_powLaw
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:40:56.745613+00:00
-- url     : https://prove2.me/submissions/7708676e-a3cd-4fcd-bc0e-98ee3dc3c494

-- Sol generated from MachineLearning/TotalVariation/Testing.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_EventSup
import Definitions.Def_MachineLearning_TotalVariation_Testing
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Operational consequences of the sharp total-variation normalization

`MachineLearning.TotalVariation.EventSup` proved the factor-`1/2` characterization

`d_TV(p, q) = max_{A} (p(A) − q(A))`.

Here we cash it in.  Three classical pillars of statistical learning theory are
derived, each of them *tight* precisely because the normalization is the sharp
one:

1. **Le Cam's two-point bound.**  For the uniform-prior binary testing problem
   `p` vs `q`, the Bayes error of the best test is exactly `(1 − d_TV)/2`
   (`isLeast_bayesError`).  With the crude `ℓ¹` normalization one would only get
   the vacuous `(1 − ‖p − q‖₁)/2`, which is negative as soon as `‖p − q‖₁ > 1`.
2. **Data processing.**  Post-processing by an arbitrary stochastic channel — in
   particular by any deterministic feature map / statistic — cannot increase
   total variation (`tvDist_channel_le`, `tvDist_map_le`).
3. **Tensorization and sample complexity.**  `d_TV(p^{⊗n}, q^{⊗n}) ≤ n·d_TV(p, q)`
   (`tvDist_powLaw_le`), so a learner needs `n ≳ 1/d_TV` i.i.d. samples before it
   can tell the two sources apart at all (`bayesError_powLaw_ge`).

## Main results

* `bayesError_eq_half_one_add_eventGap`, `isLeast_bayesError`,
  `bayesError_ge_half_one_sub_tvDist` — Le Cam;
* `tvDist_channel_le`, `tvDist_map_le` — the data-processing inequality;
* `tvDist_prodLaw_le` — two-factor tensorization (hybrid argument);
* `tvDist_powLaw_le` — the `n`-sample bound by induction;
* `bayesError_powLaw_ge` — the resulting sample-complexity lower bound.

## Application keywords

Le Cam method, hypothesis testing, data processing inequality, tensorization,
sample complexity, indistinguishability, hybrid argument
-/


open Finset

open UniversalRedundancy

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-! ## Le Cam's two-point bound -/





/-! ## The data-processing inequality -/





/-! ## Tensorization -/


lemma sum_prodLaw {p : X → ℝ} {r : Y → ℝ} (hp : ∑ x, p x = 1) (hr : ∑ y, r y = 1) :
    ∑ z, prodLaw p r z = 1 := by
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl fun x _ => by
    simpa [prodLaw] using (by rw [← Finset.mul_sum, hr, mul_one] :
      ∑ y, p x * r y = p x)]
  exact hp


/-! ## `n` i.i.d. samples -/



omit [Fintype X] in
/-- Decomposing `n + 1` samples into "first sample" and "the rest". -/
lemma powLaw_succ (p : X → ℝ) (n : ℕ) (z : X × (Fin n → X)) :
    powLaw p (n + 1) (Fin.consEquiv (fun _ => X) z) = prodLaw p (powLaw p n) z := by
  obtain ⟨a, v⟩ := z
  simp [powLaw, prodLaw, Fin.consEquiv, Fin.prod_univ_succ]






open UniversalRedundancy in
theorem solution{p : X → ℝ} (hp : ∑ x, p x = 1) : ∀ n, ∑ v, powLaw p n v = 1 := by
  intro n
  induction n with
  | zero => simp [powLaw]
  | succ n ih =>
      have hEq : ∑ v, powLaw p (n + 1) v
          = ∑ z : X × (Fin n → X), prodLaw p (powLaw p n) z := by
        rw [← Equiv.sum_comp (Fin.consEquiv (fun _ => X)) (powLaw p (n + 1))]
        exact Finset.sum_congr rfl fun z _ => powLaw_succ p n z
      rw [hEq]
      exact sum_prodLaw hp ih
