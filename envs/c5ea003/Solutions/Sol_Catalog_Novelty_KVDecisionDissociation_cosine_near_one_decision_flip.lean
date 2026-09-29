-- Prove2me | solution 1 for Catalog.Novelty.KVDecisionDissociation.cosine_near_one_decision_flip
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:04:58.531853+00:00
-- url     : https://prove2.me/submissions/ec8c4a9c-7ef7-4f80-bf9a-31ed4b3b08bf

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




/-- The *flip pair* at scale `t`: `(1+t, 1)` versus `(1, 1+t)`.
Its cosine similarity is exactly `(2 + 2t)/(t² + 2t + 2) = 1 - t²/(t²+2t+2)`. -/
theorem cosSim_flipPair (t : ℝ) :
    cosSim ![1 + t, 1] ![1, 1 + t] = (2 + 2 * t) / (t ^ 2 + 2 * t + 2) := by
  have e1 : (1 + t) ^ 2 + (1 : ℝ) ^ 2 = t ^ 2 + 2 * t + 2 := by ring
  have e2 : (1 : ℝ) ^ 2 + (1 + t) ^ 2 = t ^ 2 + 2 * t + 2 := by ring
  have hs : (0 : ℝ) ≤ t ^ 2 + 2 * t + 2 := by nlinarith [sq_nonneg (t + 1)]
  simp only [cosSim, dotP, nrmP, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    e1, e2]
  rw [Real.mul_self_sqrt hs]
  ring_nf

/-- For `t > 0` the flip pair has cosine similarity at least `1 - t/2`. -/
theorem cosSim_flipPair_lower (t : ℝ) (ht : 0 < t) :
    1 - t / 2 ≤ cosSim ![1 + t, 1] ![1, 1 + t] := by
  rw [cosSim_flipPair]
  rw [le_div_iff₀ (by nlinarith : (0:ℝ) < t ^ 2 + 2 * t + 2)]
  nlinarith [sq_nonneg t, mul_pos ht ht, sq_nonneg (t - 1)]



/-! ### 3. Why the *diffuse* tail is the fragile region -/



/-! ### 4. The two halves put together

`core_layers_agree` is the positive half (a margin certificate makes *all*
per-layer decisions agree, which is what the 22 shared layers exhibit) and
`cosine_near_one_decision_flip` is the negative half (cosine alone certifies
nothing, which is what the tail exhibits). -/



open Catalog.Novelty.KVDecisionDissociation in
theorem solution(eps : ℝ) (heps : 0 < eps) :
    ∃ u v : Fin 2 → ℝ,
      1 - eps < cosSim u v ∧ IsStrictTop u 0 ∧ IsStrictTop v 1 := by
  set t : ℝ := eps with ht
  have ht0 : 0 < t := heps
  refine ⟨![1 + t, 1], ![1, 1 + t], ?_, ?_, ?_⟩
  · have h := cosSim_flipPair_lower t ht0
    have : 1 - eps < 1 - t / 2 := by rw [ht]; linarith
    linarith
  · intro j hj
    fin_cases j
    · exact absurd rfl hj
    · simpa using by linarith
  · intro j hj
    fin_cases j
    · simpa using by linarith
    · exact absurd rfl hj
