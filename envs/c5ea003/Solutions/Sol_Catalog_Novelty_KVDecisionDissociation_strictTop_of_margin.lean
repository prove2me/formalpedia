-- Prove2me | solution 1 for Catalog.Novelty.KVDecisionDissociation.strictTop_of_margin
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:05:10.238269+00:00
-- url     : https://prove2.me/submissions/7eafef97-aa70-40c8-a18b-65d0193fc1ee

-- Sol generated from Novelty/KVDecisionDissociation.lean
import Mathlib
import Definitions.Def_Novelty_KVDecisionDissociation

/-!
# Decision–vector dissociation for attention scores (NET-51, Part A)

This file formalises the *structural* content of the NET-51 measurement
**THE-KV-CORE-IS-SHARED-THE-TAIL-IS-PERSONAL**.

The empirical situation was: two fine-tunes of the same base transformer keep
cosine-similar key/value caches at *every* layer (`cosK ≥ 0.976`, mean `0.990`),
yet in the last two layers (L22/L23) their top-1 attention decisions agree only
`0.568` / `0.627` of the time.  The slogan extracted from that measurement is

> *vector similarity does not bound functional divergence.*

Here we prove that this is not an artefact of one model pair but a theorem
about score vectors:

* `strictTop_of_margin` — the *correct* stability certificate is a **margin**
  (gap) condition: if the top-1 gap of `u` exceeds `2ε` and `u` and `v` differ
  by at most `ε` coordinatewise, then `v` makes the same decision.
* `margin_factor_two_is_sharp` — the constant `2` cannot be improved: with gap
  exactly `2ε` a perturbation of size `ε` can already destroy the decision.
* `cosine_near_one_decision_flip` — for **every** `ε > 0` there are two score
  vectors with cosine similarity `> 1 - ε` whose top-1 decisions differ.  So no
  function of the cosine alone can lower-bound decision agreement: this is the
  NET-51 dissociation, in its sharpest possible form.
* `strictTop_le_sqrt_collision` / `diffuse_decision_is_fragile` — the
  quantitative reason the *diffuse* tail is where decisions break: a small
  collision mass `∑ p k ^ 2` forces a small top-1 gap, hence a flip under an
  arbitrarily small perturbation.

Nothing here is asymptotic or approximate: all constants are explicit.
-/

open Catalog.Novelty.KVDecisionDissociation

open Finset



/-! ### 1. The correct stability certificate: margin, not cosine -/



/-! ### 2. Cosine similarity: the dissociation -/








/-! ### 3. Why the *diffuse* tail is the fragile region -/



/-! ### 4. The two halves put together

`core_layers_agree` is the positive half (a margin certificate makes *all*
per-layer decisions agree, which is what the 22 shared layers exhibit) and
`cosine_near_one_decision_flip` is the negative half (cosine alone certifies
nothing, which is what the tail exhibits). -/



open Catalog.Novelty.KVDecisionDissociation in
theorem solution{n : ℕ} (u v : Fin n → ℝ) (i : Fin n) (eps : ℝ)
    (hmargin : ∀ j, j ≠ i → 2 * eps < u i - u j)
    (hclose : ∀ j, |u j - v j| ≤ eps) : IsStrictTop v i := by
  intro j hj
  have h1 := hmargin j hj
  have h2 := abs_le.1 (hclose j)
  have h3 := abs_le.1 (hclose i)
  linarith [h2.1, h2.2, h3.1, h3.2]
