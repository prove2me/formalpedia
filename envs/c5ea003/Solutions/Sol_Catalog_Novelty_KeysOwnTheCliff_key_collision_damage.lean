-- Prove2me | solution 1 for Catalog.Novelty.KeysOwnTheCliff.key_collision_damage
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:06:48.355522+00:00
-- url     : https://prove2.me/submissions/ffc10744-12fc-41b4-a5ce-e29fe31dd9c2

-- Sol generated from Novelty/KeysOwnTheCliff.lean
import Mathlib
import Definitions.Def_Novelty_KeysOwnTheCliff

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





/-! ### 3. Keys are amplified: the query contracts against the key error -/



/-! ### 4. Two positions: tie versus decided -/

lemma attnOut_two (a b : ℝ) :
    attnOut (n := 1) ![a, b] ![1, 0] = Real.exp a / (Real.exp a + Real.exp b) := by
  simp [attnOut, softmax, Fin.sum_univ_two]

lemma attnOut_two_tie (a : ℝ) : attnOut (n := 1) ![a, a] ![1, 0] = 1 / 2 := by
  rw [attnOut_two]
  rw [div_eq_div_iff (by positivity) (by norm_num)]
  ring

/-- Three units of exponential: `exp 2 ≥ 3`. -/
lemma three_le_exp_two : (3 : ℝ) ≤ Real.exp 2 := by
  have := Real.add_one_le_exp (2 : ℝ)
  linarith

/-- A logit gap of `2` already forces the read-out past `3/4`: the softmax is a
*selection* nonlinearity, so an `O(1)` logit error is an `O(1)` output error. -/
lemma attnOut_two_gap (a b : ℝ) (h : b + 2 ≤ a) :
    3 / 4 ≤ attnOut (n := 1) ![a, b] ![1, 0] := by
  rw [attnOut_two, le_div_iff₀ (by positivity)]
  have h1 : Real.exp (b + 2) ≤ Real.exp a := Real.exp_le_exp.2 h
  have h2 : Real.exp (b + 2) = Real.exp b * Real.exp 2 := by
    rw [Real.exp_add]
  have h3 : (3 : ℝ) * Real.exp b ≤ Real.exp b * Real.exp 2 :=
    (mul_le_mul_of_nonneg_left three_le_exp_two (le_of_lt (Real.exp_pos b))).trans_eq'
      (by ring)
  linarith [h1, h2 ▸ h1]

/-! ### 5. Keys own the cliff -/



/-! ### 6. P1 refuted: no codebook of a given size can rescue the keys -/





open Catalog.Novelty.KeysOwnTheCliff in
theorem solution(a b z : ℝ) (hne : a ≠ b) :
    1 / 4 ≤ |attnOut (scores ![2 / (a - b)] ![![a], ![b]]) ![1, 0]
              - attnOut (scores ![2 / (a - b)] ![![z], ![z]]) ![1, 0]| := by
  have hab : a - b ≠ 0 := sub_ne_zero.2 hne
  have hk : scores ![2 / (a - b)] ![![a], ![b]] = ![2 / (a - b) * a, 2 / (a - b) * b] := by
    funext x
    fin_cases x <;> simp [scores]
  have hk' : scores ![2 / (a - b)] ![![z], ![z]] = ![2 / (a - b) * z, 2 / (a - b) * z] := by
    funext x
    fin_cases x <;> simp [scores]
  rw [hk, hk']
  have hgap : 2 / (a - b) * b + 2 ≤ 2 / (a - b) * a := by
    have hid : 2 / (a - b) * a - 2 / (a - b) * b = 2 := by
      field_simp
    linarith
  have h1 : 3 / 4 ≤ attnOut (n := 1) ![2 / (a - b) * a, 2 / (a - b) * b] ![1, 0] :=
    attnOut_two_gap _ _ hgap
  have h2 : attnOut (n := 1) ![2 / (a - b) * z, 2 / (a - b) * z] ![1, 0] = 1 / 2 :=
    attnOut_two_tie _
  rw [h2, abs_of_nonneg (by linarith)]
  linarith
