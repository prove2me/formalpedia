-- Prove2me | Theorems.Thm_SocialChoice_even_incoherenceIndex
-- name    : SocialChoice.even_incoherenceIndex
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:03:02.774562+00:00
-- url     : https://prove2.me/theorems/1ff134f9-8cac-4cd1-94aa-0ab836eddb70
-- title:
--   Even incoherenceIndex
-- statement:
--   Formal statement of `SocialChoice.even_incoherenceIndex` from the Aether Catalog (Applications). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem SocialChoice.even_incoherenceIndex{n : ℕ} (hd : 2 ∣ n)
--       (F : Frame n) (hpar : ∀ a ∈ F, (ZMod.castHom hd (ZMod 2)) a = 1) :
--       Even (incoherenceIndex F) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/SocialChoice/IncoherenceIndex.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/SocialChoice/IncoherenceIndex.lean#L129

-- Thm stub generated from Applications/SocialChoice/IncoherenceIndex.lean
import Mathlib
import Definitions.Def_Applications_SocialChoice_IncoherenceIndex
/-
# Realization of all even incoherence indices ≥ 4 by maximal standard frames

This file formalizes a concrete model of *standard social decision frames* and
their *incoherence index* — the length of the shortest perfectly balanced
sequence of majority-or-tie sets — and proves the realization conjecture: for
every even `n ≥ 4` there is a *maximal* standard frame whose incoherence index
is exactly `n`.  We additionally prove that `n` is the maximum index attainable
on `n` social states, that even-atom frames always have even index, and that the
spectrum of incoherence indices is unbounded.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).  Conjecture 5.7 / B.25 (MossPedersen2026, cold-start:
the referenced catalog files are not present, so we reconstruct a faithful model
from the informal description).  For every even `n ≥ 4` some maximal standard
social decision frame has incoherence index exactly `n`.

EXPERIMENT (Experimenter).  Model a frame as a finite set `F ⊆ ZMod n` of atoms;
a perfectly balanced sequence is a non-empty list of atoms summing to `0`; the
incoherence index is the infimum of the lengths of such sequences.  The
single-generator cyclic frame `{1} ⊆ ZMod n` has additive order `n`, so its
shortest zero-sum sequence is `1` repeated `n` times.  Computationally
(`ComputationalEvidence.md`) the index equals `n` for all tested `n`.

ANALYSIS (Analyst).  The result is "true and provable" via the additive order of
a unit.  Crucially `n` is also an *upper* bound on the index of any non-empty
frame (repeat one atom `n` times), so the cyclic frame attains the maximum.
Saturating a frame with more odd atoms only shortens balanced sequences (e.g.
`{1,3} ⊆ ZMod 4` has index `2`), so the extremal value is achieved by the sparse
maximal frame — the structural heart of the conjecture.

CRITIQUE (Critic).  Guards installed: `realization_even` produces a frame that is
provably maximal (`IsMaximal`, atoms generate `⊤`), the index equality is proved
by antisymmetry (not `rfl`/`decide`), and `even_incoherenceIndex` shows the value
is genuinely even.  No theorem is vacuous: each existential exhibits a concrete
witness with a nontrivial computed index.

SYNTHESIS (PI).  `realization_even` + `incoherenceIndex_isGreatest` give: the
maximum incoherence index over `n` states is `n`, attained by a maximal frame,
and every even `n ≥ 4` is realized.  See `FUTURE_DIRECTIONS.md`.
-- !-- Lab Notes -- !--
-/

open SocialChoice

open scoped BigOperators






/-
The cyclic frame `{1} ⊆ ZMod n` is maximal: the unit `1` generates the group.
-/

/-
Repeating any single atom `n` times yields a balanced sequence, so the
incoherence index of any non-empty frame is at most `n`.
-/

/-
The incoherence index of the cyclic frame `{1} ⊆ ZMod n` is exactly `n`.
-/



/-
For even `n`, frames all of whose atoms are "odd" (sent to `1` by the parity
character `ZMod n → ZMod 2`) have even incoherence index.
-/

theorem SocialChoice.even_incoherenceIndex{n : ℕ} (hd : 2 ∣ n)
    (F : Frame n) (hpar : ∀ a ∈ F, (ZMod.castHom hd (ZMod 2)) a = 1) :
    Even (incoherenceIndex F) := by sorry
