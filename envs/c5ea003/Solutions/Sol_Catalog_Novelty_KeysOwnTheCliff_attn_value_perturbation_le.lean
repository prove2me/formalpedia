-- Prove2me | solution 1 for Catalog.Novelty.KeysOwnTheCliff.attn_value_perturbation_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:06:47.262398+00:00
-- url     : https://prove2.me/submissions/6c2d2cf8-d7a7-4fca-98d9-fc876409e2eb

-- Sol generated from Novelty/KeysOwnTheCliff.lean
import Mathlib
import Definitions.Def_Novelty_KeysOwnTheCliff
import Theorems.Thm_Catalog_Novelty_KeysOwnTheCliff_softmax_pos
import Theorems.Thm_Catalog_Novelty_KeysOwnTheCliff_softmax_sum_one

/-!
# Keys own the cliff: the structural asymmetry of KV-cache quantisation (NET-93)

The NET-93 measurement (llama-perplexity, ctx = 2048, 250KB held-out wikitext
slice) produced a four-order-of-magnitude asymmetry between the two halves of
the attention cache:

| arm            | PPL      | dPPL vs control |
|----------------|----------|-----------------|
| K q4_1 / V q4_1| 3158.07  | +44,322%        |
| K iq4_nl/V iq4_nl | 1627.35 | +22,790%      |
| K q4_0 / V f16 | 2537.80  | +35,597%        |
| K f16 / V q4_0 | 7.1211   | +0.166%         |

Two claims were extracted:

* **P1 (refuted empirically).**  A richer 4-bit block format (scale + offset
  `q4_1`, or the nonuniform codebook `iq4_nl`) rescues the keys.  It does not.
* **P2 (confirmed beyond prediction).**  Keys are astronomically more sensitive
  than values; the measured damage ratio is ~2.1 · 10⁵, not the predicted ≥ 5.

This file proves that both facts are *theorems about the attention functional*,
not artefacts of one implementation family inside `llama.cpp`.

Main results.

* `attn_value_perturbation_le` — **values are free, unconditionally.**  Softmax
  weights form a convex combination, so a `δ`-perturbation of the value cache
  moves the attention output by at most `δ`: the map is `1`-Lipschitz in the
  values, with no dependence on the query, the scores, the context length or
  the depth.  (`attn_value_perturbation_sharp`: the constant `1` is attained.)
* `score_error_le_of_key_error` / `score_error_dim_amplified` — **keys are
  amplified before the nonlinearity.**  A key perturbation is contracted with
  the query, so a `δ`-perturbation of the keys moves the *logits* by up to
  `‖q‖₁ · δ`, and this dimension-times-query-norm amplification is attained.
* `key_quantization_annihilates` — for *every* resolution `δ > 0` there is a
  configuration in which a `δ`-key-perturbation moves the output by at least
  `1/4`, i.e. by a constant independent of `δ`.
* `damage_ratio_unbounded` — hence the K-vs-V damage ratio admits **no finite
  upper bound**: the measured 2.1 · 10⁵ is not a ceiling.
* `no_codebook_rescues_keys` — **P1, refuted structurally.**  For *any* key
  quantiser whatsoever whose per-block codebook has at most `N` entries —
  uniform `q4_0`, affine `q4_1`, nonuniform `iq4_nl`, or any format not yet
  invented — there are two keys separated by at least `1/N` that the codebook
  identifies, and a query of norm at most `2N` under which the exact attention
  output and the quantised one differ by at least `1/4`.  Only the *cardinality*
  of the codebook enters; no amount of representational cleverness helps.
* `value_codebook_damage_le` — the contrast: the same pigeonhole argument
  applied to a value codebook of resolution `δ` yields damage at most `δ`.

The mechanism the theorems isolate is exactly the one conjectured in NET-93:
key error enters *multiplicatively, upstream of the softmax*, where it is scaled
by the query norm and then passed through a selection nonlinearity; value error
enters *additively, downstream*, where a convex combination averages it away.
-/

open Catalog.Novelty.KeysOwnTheCliff

open Finset

variable {n d : ℕ}

/-! ### 1. The attention functional -/







/-! ### 2. Values are free: the read-out is `1`-Lipschitz downstream -/

/-- A convex combination is non-expansive in the sup-norm: this is the whole
reason a quantised **value** cache is harmless. -/
theorem convex_combination_nonexpansive {m : ℕ} (p v w : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (eps : ℝ) (h : ∀ i, |v i - w i| ≤ eps) :
    |∑ i, p i * v i - ∑ i, p i * w i| ≤ eps := by
  have hrw : ∑ i, p i * v i - ∑ i, p i * w i = ∑ i, p i * (v i - w i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hrw]
  calc |∑ i, p i * (v i - w i)| ≤ ∑ i, |p i * (v i - w i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, p i * eps := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (hp i)]
        exact mul_le_mul_of_nonneg_left (h i) (hp i)
    _ = eps := by rw [← Finset.sum_mul, hsum, one_mul]




/-! ### 3. Keys are amplified: the query contracts against the key error -/



/-! ### 4. Two positions: tie versus decided -/





/-! ### 5. Keys own the cliff -/



/-! ### 6. P1 refuted: no codebook of a given size can rescue the keys -/





open Catalog.Novelty.KeysOwnTheCliff in
theorem solution(s v w : Fin (n + 1) → ℝ) (eps : ℝ)
    (h : ∀ i, |v i - w i| ≤ eps) : |attnOut s v - attnOut s w| ≤ eps :=
  convex_combination_nonexpansive _ _ _ (fun i => le_of_lt (softmax_pos s i))
    (softmax_sum_one s) eps h
