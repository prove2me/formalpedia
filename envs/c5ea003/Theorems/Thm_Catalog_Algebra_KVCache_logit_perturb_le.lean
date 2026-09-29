-- Prove2me | Theorems.Thm_Catalog_Algebra_KVCache_logit_perturb_le
-- name    : Catalog.Algebra.KVCache.logit_perturb_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:28:10.783402+00:00
-- url     : https://prove2.me/theorems/ff7b71ce-b1b7-4fe5-9e62-42068be77b53
-- title:
--   A per-coordinate key perturbation of size `η` moves the logit by at most `d·Q·η`,
-- statement:
--   A per-coordinate key perturbation of size `η` moves the logit by at most `d·Q·η`,
--   where `Q` bounds the query coordinates.  Unlike the value path, the key path is
--   *dimension amplifying*: the head dimension multiplies the quantisation step.
--
--   ```lean
--   theorem Catalog.Algebra.KVCache.logit_perturb_le{d : ℕ} (q k g : Fin d → ℝ) (Q η : ℝ) (hQ : 0 ≤ Q)
--       (hq : ∀ c, |q c| ≤ Q) (hg : ∀ c, |g c| ≤ η) :
--       |dot q (fun c => k c + g c) - dot q k| ≤ d * Q * η := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/KVCacheRoleSplit.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/KVCacheRoleSplit.lean#L178

-- Thm stub generated from Algebra/KVCacheRoleSplit.lean
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








/-! ## The value path: linear, dimension free, `1`-Lipschitz -/


/-! ## The key path: through an inner product and an exponential -/

theorem Catalog.Algebra.KVCache.logit_perturb_le{d : ℕ} (q k g : Fin d → ℝ) (Q η : ℝ) (hQ : 0 ≤ Q)
    (hq : ∀ c, |q c| ≤ Q) (hg : ∀ c, |g c| ≤ η) :
    |dot q (fun c => k c + g c) - dot q k| ≤ d * Q * η := by sorry
