-- Prove2me | solution 1 for Catalog.Algebra.KVCache.softmaxW_perturb_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:53:26.094662+00:00
-- url     : https://prove2.me/submissions/684a7193-47f7-4123-bb5d-f4c66d80b23f

-- Sol generated from Algebra/KVCacheRoleSplit.lean
import Mathlib
import Definitions.Def_Algebra_KVCacheRoleSplit
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







/-! ## The value path: linear, dimension free, `1`-Lipschitz -/


/-! ## The key path: through an inner product and an exponential -/



/-! ## The two paths combined: the role-split error budget -/





open Catalog.Algebra.KVCache in
theorem solution(s d : Fin n → ℝ) (ε : ℝ) (hd : ∀ k, |d k| ≤ ε) (i : Fin n) :
    softmaxW (fun k => s k + d k) i ≤ Real.exp (2 * ε) * softmaxW s i := by
  have hZ : (0:ℝ) < ∑ k, Real.exp (s k) := sum_exp_pos s
  have hZ' : (0:ℝ) < ∑ k, Real.exp (s k + d k) := sum_exp_pos (fun k => s k + d k)
  have hnum : Real.exp (s i + d i) ≤ Real.exp ε * Real.exp (s i) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [abs_le.1 (hd i), (abs_le.1 (hd i)).2])
  have hden : Real.exp (-ε) * (∑ k, Real.exp (s k)) ≤ ∑ k, Real.exp (s k + d k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun k _ => ?_)
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [(abs_le.1 (hd k)).1])
  have hεpos : (0:ℝ) < Real.exp (-ε) := Real.exp_pos _
  unfold softmaxW
  rw [div_le_iff₀ hZ']
  have key : Real.exp (s i + d i) ≤
      Real.exp (2 * ε) * (Real.exp (s i) / ∑ k, Real.exp (s k)) *
        (Real.exp (-ε) * ∑ k, Real.exp (s k)) := by
    have : Real.exp (2 * ε) * (Real.exp (s i) / ∑ k, Real.exp (s k)) *
        (Real.exp (-ε) * ∑ k, Real.exp (s k))
        = Real.exp (2 * ε) * Real.exp (-ε) * Real.exp (s i) := by
      field_simp
    rw [this, ← Real.exp_add]
    calc Real.exp (s i + d i) ≤ Real.exp ε * Real.exp (s i) := hnum
      _ = Real.exp (2 * ε + -ε) * Real.exp (s i) := by ring_nf
  refine key.trans (mul_le_mul_of_nonneg_left hden ?_)
  positivity
