-- Prove2me | solution 1 for UniversalRedundancy.tvDist_powLaw_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:50:33.594613+00:00
-- url     : https://prove2.me/submissions/cf726dde-01a0-4253-854c-90300a78dd7a

-- Sol generated from MachineLearning/TotalVariation/Testing.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_EventSup
import Definitions.Def_MachineLearning_TotalVariation_Testing
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Theorems.Thm_UniversalRedundancy_sum_powLaw
import Theorems.Thm_UniversalRedundancy_tvDist_prodLaw_le
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




/-! ## `n` i.i.d. samples -/


omit [Fintype X] in
lemma powLaw_nonneg {p : X → ℝ} (hp0 : ∀ x, 0 ≤ p x) (n : ℕ) (v : Fin n → X) :
    0 ≤ powLaw p n v :=
  Finset.prod_nonneg fun i _ => hp0 (v i)

omit [Fintype X] in
/-- Decomposing `n + 1` samples into "first sample" and "the rest". -/
lemma powLaw_succ (p : X → ℝ) (n : ℕ) (z : X × (Fin n → X)) :
    powLaw p (n + 1) (Fin.consEquiv (fun _ => X) z) = prodLaw p (powLaw p n) z := by
  obtain ⟨a, v⟩ := z
  simp [powLaw, prodLaw, Fin.consEquiv, Fin.prod_univ_succ]


/-- Total variation is invariant under relabelling the sample space. -/
lemma tvDist_equiv_comp {Z : Type*} [Fintype Z] (e : Z ≃ X) (p q : X → ℝ) :
    tvDist (fun z => p (e z)) (fun z => q (e z)) = tvDist p q := by
  unfold tvDist
  rw [Equiv.sum_comp e fun x => |p x - q x|]




open UniversalRedundancy in
theorem solution{p q : X → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hp : ∑ x, p x = 1)
    (hq0 : ∀ x, 0 ≤ q x) (hq : ∑ x, q x = 1) :
    ∀ n : ℕ, tvDist (powLaw p n) (powLaw q n) ≤ n * tvDist p q := by
  intro n
  induction n with
  | zero => simp [powLaw, tvDist]
  | succ n ih =>
      have hEq : ∀ r : X → ℝ, (fun z : X × (Fin n → X) =>
          powLaw r (n + 1) (Fin.consEquiv (fun _ => X) z)) = prodLaw r (powLaw r n) := by
        intro r; funext z; exact powLaw_succ r n z
      have hstep : tvDist (powLaw p (n + 1)) (powLaw q (n + 1))
          = tvDist (prodLaw p (powLaw p n)) (prodLaw q (powLaw q n)) := by
        rw [← tvDist_equiv_comp (Fin.consEquiv (fun _ => X)) (powLaw p (n + 1))
          (powLaw q (n + 1)), hEq p, hEq q]
      have hbound := tvDist_prodLaw_le (p₁ := p) (q₁ := q)
        (p₂ := powLaw p n) (q₂ := powLaw q n) hq0 hq (powLaw_nonneg hp0 n) (sum_powLaw hp n)
      rw [hstep]
      have : tvDist p q + tvDist (powLaw p n) (powLaw q n) ≤ tvDist p q + n * tvDist p q := by
        linarith
      have hcast : ((n : ℝ) + 1) * tvDist p q = tvDist p q + n * tvDist p q := by ring
      push_cast
      linarith
