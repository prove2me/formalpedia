-- Prove2me | solution 1 for Catalog.Novelty.KeysOwnTheCliff.no_codebook_rescues_keys
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:08:07.010492+00:00
-- url     : https://prove2.me/submissions/901bc726-01c5-44ca-a65a-3bb7425c438d

-- Sol generated from Novelty/KeysOwnTheCliff.lean
import Mathlib
import Definitions.Def_Novelty_KeysOwnTheCliff
import Theorems.Thm_Catalog_Novelty_KeysOwnTheCliff_key_collision_damage

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





/-! ### 5. Keys own the cliff -/



/-! ### 6. P1 refuted: no codebook of a given size can rescue the keys -/





open Catalog.Novelty.KeysOwnTheCliff in
theorem solution(N : ℕ) (hN : 0 < N) (Q : ℝ → ℝ) (C : Finset ℝ)
    (hQ : ∀ x, Q x ∈ C) (hC : C.card ≤ N) :
    ∃ a b : ℝ, a ≠ b ∧ Q a = Q b ∧ (1 : ℝ) / N ≤ |a - b| ∧
      ∃ q : Fin 1 → ℝ, |q 0| ≤ 2 * N ∧
        1 / 4 ≤ |attnOut (scores q ![![a], ![b]]) ![1, 0]
                  - attnOut (scores q ![![Q a], ![Q b]]) ![1, 0]| := by
  -- Pigeonhole: `N+1` equally spaced probes cannot receive `N+1` distinct codes.
  have hcard : C.card < (Finset.univ : Finset (Fin (N + 1))).card := by
    simpa using Nat.lt_succ_of_le hC
  obtain ⟨i, -, j, -, hij, hQij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := fun i : Fin (N + 1) => Q ((i : ℝ) / N)) (fun i _ => hQ _)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hijR : ((i : ℕ) : ℝ) ≠ ((j : ℕ) : ℝ) := by
    intro h
    exact hij (Fin.ext (by exact_mod_cast h))
  have hne : ((i : ℕ) : ℝ) / N ≠ ((j : ℕ) : ℝ) / N := by
    intro h
    exact hijR (by field_simp at h; exact h)
  have hone : (1 : ℝ) ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
    rcases lt_or_gt_of_ne (fun h : (i : ℕ) = (j : ℕ) => hij (Fin.ext h)) with h | h
    · have hlt : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    · have hlt : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hsep : (1 : ℝ) / N ≤ |((i : ℕ) : ℝ) / N - ((j : ℕ) : ℝ) / N| := by
    have hsub : ((i : ℕ) : ℝ) / N - ((j : ℕ) : ℝ) / N
        = (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) / N := by ring
    rw [hsub, abs_div, abs_of_pos hNpos]
    gcongr
  refine ⟨((i : ℕ) : ℝ) / N, ((j : ℕ) : ℝ) / N, hne, hQij, hsep,
    ⟨![2 / (((i : ℕ) : ℝ) / N - ((j : ℕ) : ℝ) / N)], ?_, ?_⟩⟩
  · have hpos : 0 < |((i : ℕ) : ℝ) / N - ((j : ℕ) : ℝ) / N| := lt_of_lt_of_le (by positivity) hsep
    have hid : (2 * (N : ℝ)) * (1 / N) = 2 := by field_simp
    have hmul : (2 * (N : ℝ)) * (1 / N)
        ≤ (2 * (N : ℝ)) * |((i : ℕ) : ℝ) / N - ((j : ℕ) : ℝ) / N| := by
      exact mul_le_mul_of_nonneg_left hsep (by positivity)
    simp only [Matrix.cons_val_zero, abs_div]
    rw [div_le_iff₀ hpos]
    rw [hid] at hmul
    calc |(2 : ℝ)| = 2 := abs_of_nonneg (by norm_num)
      _ ≤ 2 * (N : ℝ) * |((i : ℕ) : ℝ) / N - ((j : ℕ) : ℝ) / N| := hmul
  · rw [← hQij]
    exact key_collision_damage _ _ (Q (((i : ℕ) : ℝ) / N)) hne
