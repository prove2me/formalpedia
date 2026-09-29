-- Prove2me | solution 1 for Catalog.Algebra.KVCache.key_path_error_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:56:39.279057+00:00
-- url     : https://prove2.me/submissions/2c7112a2-3a7a-49d9-aee1-a53bb049bb3a

-- Sol generated from Algebra/KVCacheRoleSplit.lean
import Mathlib
import Definitions.Def_Algebra_KVCacheRoleSplit
import Theorems.Thm_Catalog_Algebra_KVCache_softmaxW_l1_perturb_le
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








/-! ## The value path: linear, dimension free, `1`-Lipschitz -/


/-! ## The key path: through an inner product and an exponential -/



/-! ## The two paths combined: the role-split error budget -/





open Catalog.Algebra.KVCache in
theorem solution(s d v : Fin n → ℝ) (ε V : ℝ) (hε : 0 ≤ ε)
    (hd : ∀ k, |d k| ≤ ε) (hv : ∀ i, |v i| ≤ V) :
    |(∑ i, softmaxW (fun k => s k + d k) i * v i) - ∑ i, softmaxW s i * v i|
      ≤ 2 * (Real.exp (2 * ε) - 1) * V := by
  have hV : 0 ≤ V := le_trans (abs_nonneg (v ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩)) (hv _)
  set w := softmaxW s with hw
  set w' := softmaxW (fun k => s k + d k) with hw'
  have hrw : (∑ i, w' i * v i) - ∑ i, w i * v i = ∑ i, (w' i - w i) * v i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hrw]
  calc |∑ i, (w' i - w i) * v i| ≤ ∑ i, |(w' i - w i) * v i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |w' i - w i| * V := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _)
    _ = (∑ i, |w' i - w i|) * V := by rw [Finset.sum_mul]
    _ ≤ (2 * (Real.exp (2 * ε) - 1)) * V := by
        exact mul_le_mul_of_nonneg_right (softmaxW_l1_perturb_le s d ε hε hd) hV
    _ = 2 * (Real.exp (2 * ε) - 1) * V := by ring
