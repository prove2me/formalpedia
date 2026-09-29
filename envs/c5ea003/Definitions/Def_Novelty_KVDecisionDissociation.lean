-- Prove2me | Definitions.Def_Novelty_KVDecisionDissociation
-- name    : Novelty_KVDecisionDissociation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:29:34.469103+00:00
-- url     : https://prove2.me/theorems/9fad0e62-91af-474c-bed5-27c8785c2e29
-- title:
--   Aether Catalog definitions — Novelty_KVDecisionDissociation
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.KVDecisionDissociation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/KVDecisionDissociation.lean by skeleton subtraction
import Mathlib

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

namespace Catalog.Novelty.KVDecisionDissociation

open Finset

/-- `i` is the strict top-1 choice of the score vector `u`
(the "attention decision" of `u`). -/
def IsStrictTop {n : ℕ} (u : Fin n → ℝ) (i : Fin n) : Prop := ∀ j, j ≠ i → u j < u i

/-- A vector has *no* decision when two coordinates tie at the top. -/
def NoStrictTop {n : ℕ} (u : Fin n → ℝ) : Prop := ∀ i, ¬ IsStrictTop u i

/-! ### 1. The correct stability certificate: margin, not cosine -/



/-! ### 2. Cosine similarity: the dissociation -/

/-- Euclidean inner product of two score vectors. -/
noncomputable def dotP {n : ℕ} (u v : Fin n → ℝ) : ℝ := ∑ i, u i * v i

/-- Euclidean norm of a score vector. -/
noncomputable def nrmP {n : ℕ} (u : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, u i ^ 2)

/-- Cosine similarity, the quantity reported as `cosK` / `cosV` in NET-51. -/
noncomputable def cosSim {n : ℕ} (u v : Fin n → ℝ) : ℝ := dotP u v / (nrmP u * nrmP v)





/-! ### 3. Why the *diffuse* tail is the fragile region -/



/-! ### 4. The two halves put together

`core_layers_agree` is the positive half (a margin certificate makes *all*
per-layer decisions agree, which is what the 22 shared layers exhibit) and
`cosine_near_one_decision_flip` is the negative half (cosine alone certifies
nothing, which is what the tail exhibits). -/


end Catalog.Novelty.KVDecisionDissociation


