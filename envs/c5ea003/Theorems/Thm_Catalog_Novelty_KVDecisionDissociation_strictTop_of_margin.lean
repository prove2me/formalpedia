-- Prove2me | Theorems.Thm_Catalog_Novelty_KVDecisionDissociation_strictTop_of_margin
-- name    : Catalog.Novelty.KVDecisionDissociation.strictTop_of_margin
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:10:33.81083+00:00
-- url     : https://prove2.me/theorems/e1b33eed-25c7-4522-acd7-ad49fc39e1cc
-- title:
--   Margin stability.
-- statement:
--   **Margin stability.**  If the top-1 gap of `u` at `i` exceeds `2ε` and `v`
--   differs from `u` by at most `ε` in every coordinate, then `v` makes the same
--   top-1 decision.  This is the only sound "decisions agree" certificate.
--
--   ```lean
--   theorem Catalog.Novelty.KVDecisionDissociation.strictTop_of_margin{n : ℕ} (u v : Fin n → ℝ) (i : Fin n) (eps : ℝ)
--       (hmargin : ∀ j, j ≠ i → 2 * eps < u i - u j)
--       (hclose : ∀ j, |u j - v j| ≤ eps) : IsStrictTop v i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/KVDecisionDissociation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/KVDecisionDissociation.lean#L48

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

theorem Catalog.Novelty.KVDecisionDissociation.strictTop_of_margin{n : ℕ} (u v : Fin n → ℝ) (i : Fin n) (eps : ℝ)
    (hmargin : ∀ j, j ≠ i → 2 * eps < u i - u j)
    (hclose : ∀ j, |u j - v j| ≤ eps) : IsStrictTop v i := by sorry
