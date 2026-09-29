-- Prove2me | Definitions.Def_Novelty_KeysOwnTheCliff
-- name    : Novelty_KeysOwnTheCliff
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:29:33.198469+00:00
-- url     : https://prove2.me/theorems/21dd48d0-d0f8-4d20-8f9f-9ba483cec2b1
-- title:
--   Aether Catalog definitions — Novelty_KeysOwnTheCliff
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.KeysOwnTheCliff`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/KeysOwnTheCliff.lean by skeleton subtraction
import Mathlib

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

namespace Catalog.Novelty.KeysOwnTheCliff

open Finset

variable {n d : ℕ}

/-! ### 1. The attention functional -/

/-- Softmax over `n+1` cached positions. -/
noncomputable def softmax (s : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  Real.exp (s i) / ∑ j, Real.exp (s j)

/-- Single-head attention read-out: the softmax-weighted average of the values. -/
noncomputable def attnOut (s v : Fin (n + 1) → ℝ) : ℝ := ∑ i, softmax s i * v i

/-- The logits produced by a query `q` against a key cache `k`. -/
def scores (q : Fin d → ℝ) (k : Fin (n + 1) → Fin d → ℝ) : Fin (n + 1) → ℝ :=
  fun i => ∑ t, q t * k i t




/-! ### 2. Values are free: the read-out is `1`-Lipschitz downstream -/





/-! ### 3. Keys are amplified: the query contracts against the key error -/



/-! ### 4. Two positions: tie versus decided -/





/-! ### 5. Keys own the cliff -/



/-! ### 6. P1 refuted: no codebook of a given size can rescue the keys -/




end Catalog.Novelty.KeysOwnTheCliff


