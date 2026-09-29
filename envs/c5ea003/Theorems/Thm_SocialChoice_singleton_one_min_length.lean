-- Prove2me | Theorems.Thm_SocialChoice_singleton_one_min_length
-- name    : SocialChoice.singleton_one_min_length
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:03:33.804347+00:00
-- url     : https://prove2.me/theorems/3e69a41b-f785-4662-8533-ef11f3157c78
-- title:
--   Every balanced sequence of `{1} ⊆ ZMod n` has length at least `n`
-- statement:
--   Every balanced sequence of `{1} ⊆ ZMod n` has length at least `n`
--   (reproduced).
--
--   ```lean
--   theorem SocialChoice.singleton_one_min_length{n : ℕ} (l : List (ZMod n))
--       (h : IsBalanced ({1} : Frame n) l) : n ≤ l.length := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/SocialChoice/IncoherenceStratification.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/SocialChoice/IncoherenceStratification.lean#L95

-- Thm stub generated from Applications/SocialChoice/NonFiniteAxiomatization.lean
import Mathlib
import Definitions.Def_Applications_SocialChoice_NonFiniteAxiomatization
/-
# Non-finite-axiomatization of measurable majorities via the incoherence index

This file extends the catalog model of *standard social decision frames* from
`Applications/SocialChoice/IncoherenceIndex.lean` (the reconstructed
`MossPedersen2026` / `arXiv:2606.23853` framework: frames as finite atom sets in
`ZMod n`, *perfectly balanced sequences*, and the *incoherence index*).  Because
the surrounding monorepo's build configuration does not make that module
importable in isolation, the small amount of shared infrastructure (the model
definitions and three base lemmas about the single-generator frame) is
reproduced here verbatim from the catalog file; the **main results below are new**:

* `realization_2k2` — for every `k ≥ 1` a *maximal* frame whose shortest
  coherence violation has length exactly `2k+2` (every even index `≥ 4`).
* `coherence_not_finitely_axiomatizable` — no bounded finite fragment can replace
  the coherence criterion (the headline non-finite-axiomatization theorem).
* `incoherenceIndex_unbounded_over_maximal` — the spectrum of incoherence indices
  over maximal frames is unbounded.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).  Bold conjecture: coherence (= strict majority
representability) is *not* finitely axiomatizable.  For no fixed `B` does "no
perfectly balanced sequence of length `≤ B`" imply "no perfectly balanced
sequence at all", uniformly over all finite social decision frames.  The
obstruction is quantitative: incoherence indices realize the entire even tail
`2k+2`, so any finite bound is eventually overshot.

EXPERIMENT (Experimenter).  Reuse the catalog model.  The single-generator frame
`{1} ⊆ ZMod n` is maximal and its shortest balanced sequence is `1` repeated `n`
times (`incoherenceIndex_singleton_one`).  Set `n = 2k+2` to hit every even
length `≥ 4`; set `n = B+1` to defeat the width-`B` fragment.  The decisive new
lemma `singleton_one_min_length` shows every balanced sequence of `{1}` has
length `≥ n` (all atoms equal `1`, so the length is a positive multiple of `n`).

ANALYSIS (Analyst).  True and provable.  Structural pattern: the incoherence
index of `{1} ⊆ ZMod n` equals the additive order `n` of the unit, so the family
`{1} ⊆ ZMod (B+1)` produces, for each `B`, a frame that passes the width-`B`
test yet is genuinely incoherent — exactly a non-finite-axiomatization failure:
the bounded fragments are strictly weaker than the full criterion at every stage.

CRITIQUE (Critic).  Guards: `coherence_not_finitely_axiomatizable` is proved by
`by_contra` (no `decide`/`rfl` shortcut); every witness frame is exhibited
maximal; the separating gap is quantitative (`B < l.length`).  No theorem is
vacuous: each existential carries a concrete frame with a computed index, and the
separating frame is simultaneously coherent-up-to-`B` and incoherent.

SYNTHESIS (PI).  Together with the catalog's `realization_even`, these results
upgrade "the spectrum is unbounded" to "the criterion admits no bounded finite
fragment" — the precise sense in which measurable majorities cannot be finitely
axiomatized.  See `FUTURE_DIRECTIONS.md`.
-- !-- Lab Notes -- !--
-/

open SocialChoice

open scoped BigOperators

/-! ## Catalog model (reproduced from `IncoherenceIndex.lean`) -/









/-! ## New results: non-finite-axiomatization -/

/-
Every perfectly balanced sequence of the single-generator frame `{1}` has a
length divisible by `n`: all its atoms equal `1`, so its length is a multiple of
the additive order `n`.
-/

/-
Every perfectly balanced sequence of the single-generator frame `{1} ⊆ ZMod n`
has length at least `n` (its incoherence index).
-/

theorem SocialChoice.singleton_one_min_length{n : ℕ} (l : List (ZMod n))
    (h : IsBalanced ({1} : Frame n) l) : n ≤ l.length := by sorry
