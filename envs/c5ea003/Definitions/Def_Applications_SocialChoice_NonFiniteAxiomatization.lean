-- Prove2me | Definitions.Def_Applications_SocialChoice_NonFiniteAxiomatization
-- name    : Applications_SocialChoice_NonFiniteAxiomatization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:55.520599+00:00
-- url     : https://prove2.me/theorems/3954f484-f9c8-4519-925b-4b48c147e2e5
-- title:
--   Aether Catalog definitions — Applications_SocialChoice_NonFiniteAxiomatization
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.SocialChoice.NonFiniteAxiomatization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/SocialChoice/NonFiniteAxiomatization.lean by skeleton subtraction
import Mathlib
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

namespace SocialChoice

open scoped BigOperators

/-! ## Catalog model (reproduced from `IncoherenceIndex.lean`) -/

/-- A *standard social decision frame* on `n` social states: a finite set of
"majority-or-tie" residues (atoms) in `ZMod n`. -/
abbrev Frame (n : ℕ) := Finset (ZMod n)

/-- A *perfectly balanced sequence* for a frame `F`: a non-empty list of atoms of
`F` whose sum vanishes in `ZMod n`. -/
def IsBalanced {n : ℕ} (F : Frame n) (l : List (ZMod n)) : Prop :=
  l ≠ [] ∧ (∀ x ∈ l, x ∈ F) ∧ l.sum = 0

/-- The set of lengths of perfectly balanced sequences of `F`. -/
def balancedLengths {n : ℕ} (F : Frame n) : Set ℕ :=
  { k | ∃ l, IsBalanced F l ∧ l.length = k }

/-- The *incoherence index*: the length of the shortest perfectly balanced
sequence (`0` if no balanced sequence exists). -/
noncomputable def incoherenceIndex {n : ℕ} (F : Frame n) : ℕ :=
  sInf (balancedLengths F)

/-- A frame is *maximal* when its atoms generate the whole decision space. -/
def IsMaximal {n : ℕ} (F : Frame n) : Prop :=
  AddSubgroup.closure (F : Set (ZMod n)) = ⊤




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

/-
**Parametric realization.** For every `k ≥ 1` there is a *maximal* standard
social decision frame whose shortest coherence violation has length exactly
`2k+2`.  This exhibits every even index `≥ 4` and shows no uniform finite bound
caps the incoherence index.
-/

/-- A frame is *coherent* (strict-majority representable) when it admits no
perfectly balanced sequence at all. -/
def Coherent {n : ℕ} (F : Frame n) : Prop :=
  ¬ ∃ l, IsBalanced F l

/-- The *width-`B` finite fragment*: a frame passes it when it admits no perfectly
balanced sequence of length `≤ B`.  This is the candidate bounded replacement for
the (infinitary) coherence criterion. -/
def CoherentUpTo {n : ℕ} (B : ℕ) (F : Frame n) : Prop :=
  ¬ ∃ l, IsBalanced F l ∧ l.length ≤ B

/-
Genuine coherence always implies passing every finite fragment.
-/

/-
The single-generator frame `{1} ⊆ ZMod (B+1)` is genuinely incoherent: it
admits the balanced sequence `1` repeated `B+1` times.
-/

/-
The single-generator frame `{1} ⊆ ZMod (B+1)` passes the width-`B` fragment:
its shortest balanced sequence has length `B+1 > B`.
-/

/-
**Non-finite-axiomatization (existential form).** For every finite bound `B`
there is a *maximal* standard frame that passes the width-`B` fragment yet is
genuinely incoherent.  Hence no finite fragment captures coherence.
-/

/-
**Non-finite-axiomatization (headline).** It is impossible to replace the
coherence criterion for strict majority representability by any bounded finite
fragment: there is no width `B` for which "no balanced violation of length `≤ B`"
is equivalent to full coherence across all finite social decision frames.
-/

/-
**Unboundedness over maximal frames.** For every `N` there is a maximal
standard frame whose incoherence index exceeds `N`, realized by the explicit
`2k+2` family.  This is the quantitative engine behind non-finite-axiomatization.
-/

end SocialChoice


