-- Prove2me | Theorems.Thm_Catalog_Novelty_KVDecisionDissociation_cosine_near_one_decision_flip
-- name    : Catalog.Novelty.KVDecisionDissociation.cosine_near_one_decision_flip
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:09:55.484934+00:00
-- url     : https://prove2.me/theorems/d271a26a-36ee-44f5-8caf-6623b387b0a5
-- title:
--   The NET-51 dissociation.
-- statement:
--   **The NET-51 dissociation.**  For every `ε > 0` there are two score vectors
--   whose cosine similarity exceeds `1 - ε` but whose top-1 attention decisions are
--   *different*.  Consequently no monotone function of the cosine similarity can be
--   a lower bound for top-1 decision agreement: the observed
--   `cos = 0.983` with agreement `0.568` at layer 22 is structurally possible.
--
--   ```lean
--   theorem Catalog.Novelty.KVDecisionDissociation.cosine_near_one_decision_flip(eps : ℝ) (heps : 0 < eps) :
--       ∃ u v : Fin 2 → ℝ,
--         1 - eps < cosSim u v ∧ IsStrictTop u 0 ∧ IsStrictTop v 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/KVDecisionDissociation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/KVDecisionDissociation.lean#L118

-- Thm stub generated from Novelty/KVDecisionDissociation.lean
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

theorem Catalog.Novelty.KVDecisionDissociation.cosine_near_one_decision_flip(eps : ℝ) (heps : 0 < eps) :
    ∃ u v : Fin 2 → ℝ,
      1 - eps < cosSim u v ∧ IsStrictTop u 0 ∧ IsStrictTop v 1 := by sorry
