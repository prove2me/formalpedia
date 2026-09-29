-- Prove2me | solution 1 for Catalog.Algebra.KVCache.softmaxW_l1_perturb_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:55:14.011736+00:00
-- url     : https://prove2.me/submissions/aa3b91b3-4107-4171-8bdc-3cc036351f8e

-- Sol generated from Algebra/KVCacheRoleSplit.lean
import Mathlib
import Definitions.Def_Algebra_KVCacheRoleSplit
import Theorems.Thm_Catalog_Algebra_KVCache_softmaxW_perturb_le
/-
# The algebra of role-asymmetric KV-cache quantisation

This file formalises the *mechanism* behind the NET-94 experimental cell
(`llama-perplexity`, ctx = 2048, 250 KB held-out wikitext slice):

| arm                | PPL     | dPPL vs f16 |
|--------------------|---------|-------------|
| K `q8_0` / V `q4_0`| 7.1194  | +0.142 %    |
| K `q5_1` / V `q5_1`| 68.7963 | +867.694 %  |

The measurement says that the two halves of an attention cache behave completely
differently under quantisation: keys are fragile, values are free.  The purpose of
this file is to show that this asymmetry is not an empirical accident but an
algebraic consequence of *where* the two tensors enter the attention map.

* A **value** enters the attention output **linearly**, inside a convex combination.
  A perturbation of size `ε` moves the output by at most `ε`: the value path is a
  `1`-Lipschitz averaging operator (`value_path_stable`), and its distortion is
  *dimension free*.
* A **key** enters through the **exponential** of an inner product with the query.
  Perturbing the key by `η` per coordinate moves the logit by up to `d·Q·η`
  (`logit_perturb_le`) and the softmax weights by a factor `exp (2 d Q η)`
  (`softmaxW_perturb_le`).  That factor is *attained*: the log-odds of the softmax
  are translated *exactly* by the logit perturbation (`softmaxW_odds_shift`), so no
  sharper bound exists.

The two facts together are the `role split`:  a uniform per-coordinate budget `η`
costs `O(η)` on the value side and `Θ(exp (d Q η))` on the key side.

Main results
* `softmaxW_sum_one`, `softmaxW_pos` — the softmax is a probability vector.
* `softmaxW_odds_shift` — exact translation of the log-odds (tightness of the key bound).
* `softmaxW_perturb_le` — `exp (2ε)` multiplicative stability of softmax weights.
* `softmaxW_l1_perturb_le` — the induced `ℓ¹` movement of the weight vector.
* `value_path_stable` — the value path is `1`-Lipschitz (no amplification whatsoever).
* `key_path_error_le` / `attention_split_error_le` — the full role-split error budget.
* `role_asymmetry` — for a common per-coordinate budget the key bound is at least
  `d·Q` times the value bound, and grows exponentially, while the value bound is linear.
-/

open Catalog.Algebra.KVCache

open Finset

/-! ## Softmax weights -/


variable {n : ℕ} [NeZero n]

lemma sum_exp_pos (s : Fin n → ℝ) : 0 < ∑ j, Real.exp (s j) := by
  have : (Finset.univ : Finset (Fin n)).Nonempty := by
    have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
    exact Finset.univ_nonempty
  exact Finset.sum_pos (fun j _ => Real.exp_pos _) this

lemma softmaxW_pos (s : Fin n → ℝ) (i : Fin n) : 0 < softmaxW s i :=
  div_pos (Real.exp_pos _) (sum_exp_pos s)

lemma softmaxW_nonneg (s : Fin n → ℝ) (i : Fin n) : 0 ≤ softmaxW s i :=
  (softmaxW_pos s i).le

@[simp] lemma softmaxW_sum_one (s : Fin n → ℝ) : ∑ i, softmaxW s i = 1 := by
  unfold softmaxW
  rw [← Finset.sum_div, div_self (ne_of_gt (sum_exp_pos s))]




/-! ## The value path: linear, dimension free, `1`-Lipschitz -/


/-! ## The key path: through an inner product and an exponential -/



/-! ## The two paths combined: the role-split error budget -/





open Catalog.Algebra.KVCache in
theorem solution(s d : Fin n → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hd : ∀ k, |d k| ≤ ε) :
    ∑ i, |softmaxW (fun k => s k + d k) i - softmaxW s i| ≤ 2 * (Real.exp (2 * ε) - 1) := by
  set w := softmaxW s with hw
  set w' := softmaxW (fun k => s k + d k) with hw'
  have hsum0 : ∑ i, (w' i - w i) = 0 := by
    rw [Finset.sum_sub_distrib, hw, hw', softmaxW_sum_one, softmaxW_sum_one, sub_self]
  have habs : ∀ i : Fin n, |w' i - w i| = 2 * max (w' i - w i) 0 - (w' i - w i) := by
    intro i
    by_cases h : 0 ≤ w' i - w i
    · rw [abs_of_nonneg h, max_eq_left h]; ring
    · push_neg at h
      rw [abs_of_neg h, max_eq_right h.le]; ring
  have hpos : ∀ i : Fin n, max (w' i - w i) 0 ≤ (Real.exp (2 * ε) - 1) * w i := by
    intro i
    have h1 : w' i ≤ Real.exp (2 * ε) * w i := softmaxW_perturb_le s d ε hd i
    have h2 : (0:ℝ) ≤ (Real.exp (2 * ε) - 1) * w i := by
      have : (1:ℝ) ≤ Real.exp (2 * ε) := Real.one_le_exp (by linarith)
      have := softmaxW_nonneg s i
      nlinarith
    exact max_le (by nlinarith) h2
  calc ∑ i, |w' i - w i|
      = ∑ i, (2 * max (w' i - w i) 0 - (w' i - w i)) := by
        exact Finset.sum_congr rfl (fun i _ => habs i)
    _ = 2 * ∑ i, max (w' i - w i) 0 - ∑ i, (w' i - w i) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = 2 * ∑ i, max (w' i - w i) 0 := by rw [hsum0]; ring
    _ ≤ 2 * ∑ i, (Real.exp (2 * ε) - 1) * w i := by
        have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpos i)
        linarith
    _ = 2 * (Real.exp (2 * ε) - 1) := by
        rw [← Finset.mul_sum, hw, softmaxW_sum_one, mul_one]
