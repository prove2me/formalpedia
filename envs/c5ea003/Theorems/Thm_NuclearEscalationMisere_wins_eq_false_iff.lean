-- Prove2me | Theorems.Thm_NuclearEscalationMisere_wins_eq_false_iff
-- name    : NuclearEscalationMisere.wins_eq_false_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:18:24.933231+00:00
-- url     : https://prove2.me/theorems/e2c7d65b-a7fe-4a92-a21a-d3b199fc54ed
-- title:
--   Main theorem (corrected conjecture).
-- statement:
--   **Main theorem (corrected conjecture).**  For granularity `m ≥ 1`, the misère
--   P‑positions of the single‑theater escalation game are exactly the positions with
--   `r ≡ 1 (mod m+1)`.
--
--   ```lean
--   theorem NuclearEscalationMisere.wins_eq_false_iff(m : ℕ) (hm : 1 ≤ m) (r : ℕ) :
--       wins m r = false ↔ r % (m + 1) = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/NuclearEscalationMisere.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/NuclearEscalationMisere.lean#L161

-- Thm stub generated from Novelty/NuclearEscalationMisere.lean
import Mathlib
import Definitions.Def_Novelty_NuclearEscalationMisere

/-!
# Eventual congruence of misère P‑positions in nuclear escalation ladders

This file formalizes the *single‑theater escalation game* and analyzes its
**misère** P‑positions.

## The game (Definition 1)

Fix an *escalation granularity* `m ≥ 1`.  A position is a natural number `r`, the
number of *remaining rungs* on the escalation ladder.  A move descends the ladder
by `s ∈ {1, …, m}` rungs, so from `r` one may move to any of `r-1, …, r-min(m,r)`.
Position `0` (fully escalated) is terminal.  Under **misère** play the player who
is forced to make the final escalation *loses*; equivalently, the player to move
at the terminal position `0` *wins*.

We encode the outcome by a Boolean `wins m r`, `true` iff the player to move wins.
A **P‑position** (previous‑player win, i.e. the player to move loses) is
`wins m r = false`.

## Main results

* `wins_eq_false_iff` : for `m ≥ 1`, the misère P‑positions are **exactly**
  `r ≡ 1 (mod m+1)` — for *all* `r`, hence a fortiori for all sufficiently long
  ladders.  This is the corrected form of the research conjecture.
* `misere_eventual_congruence` : the "eventual congruence" statement of the
  research brief, in its corrected form (the congruence holds for every ladder
  length, with threshold `T(m) = 0`).
* `winsN_eq_false_iff` : the *normal‑play* companion.  Its P‑positions are exactly
  `r ≡ 0 (mod m+1)` — these are the Sprague–Grundy zero positions of the
  subtraction game `{1,…,m}`.
* `misere_conjecture_false` : the research conjecture **as literally stated**
  (misère P‑positions `≡ 0 (mod m+1)`) is *false*; the residue `0` is the normal‑
  play answer, while misère gives residue `1`.

-- !-- Lab Notes -- !--

### Hypothesis (Hypothesizer)
The brief conjectures that misère P‑positions of the escalation game Filter.eventually
satisfy `r ≡ 0 (mod m+1)`.  Candidate falsifiable conjectures generated:
 (H1) misère P‑positions are `r ≡ 0 (mod m+1)` [the brief].
 (H2, surprising) misère P‑positions are `r ≡ 1 (mod m+1)` — a *shift* of the
     normal‑play answer.
 (H3) the characterization holds for ALL `r`, not merely "Filter.eventually" (T(m)=0).
 (H4) normal‑play P‑positions are `r ≡ 0 (mod m+1)` (Sprague–Grundy).
 (H5, counter‑intuitive) the misère and normal answers are *never* equal for any
     residue, so H1 and H4 cannot both hold — one convention is misattributed.

### Experiment (Experimenter)
Boolean game solver computed `wins m r` for `m ∈ {1,2,3}`, `r ≤ 40`:
  m=1: P at 1,3,5,7,9,11,…   → r ≡ 1 (mod 2)
  m=2: P at 1,4,7,10,…       → r ≡ 1 (mod 3)
  m=3: P at 1,5,9,…          → r ≡ 1 (mod 4)
Normal play `winsN`:
  m=2: P at 0,3,6,9,…        → r ≡ 0 (mod 3)
This falsifies H1 and confirms H2, H3, H4, H5.

### Analysis (Analyst)
The crux is a modulus‑arithmetic fact (`nt_iff`): among the `q-1` predecessors
`pos-1,…,pos-(q-1)` of `pos` (capped at `0`), *none* is `≡ t (mod q)` iff
`pos ≡ t (mod q)`, valid for the target residues `t ∈ {0,1}`.  The forward
direction is a clean `s ≡ 0 (mod q)` contradiction; the backward direction
exhibits an explicit predecessor.  Feeding this through a strong induction on `r`
and the move‑unfolding lemma `wins_succ_true_iff` yields the characterization.
"True but subtle": the misère answer is `1`, not `0`; the brief conflated the two
play conventions (the `0` congruence is the *normal*-play / Sprague–Grundy fact).

### Critique (Critic)
The conjecture is refuted (`misere_conjecture_false`) rather than silently fixed;
the honest statement is retained.  No theorem is vacuous: `wins_eq_false_iff` is a
genuine ↔ over all `r`; `misere_conjecture_false` is a nontrivial negation proved
via the characterization; `winsN_eq_false_iff` is the independent normal‑play
result.  Definitions are computable and were cross‑checked numerically.

### Synthesis (PI)
The single‑theater escalation game is a subtraction game `{1,…,m}`.  Its misère
theory *shifts* the normal‑play congruence class from `0` to `1`.  The "eventual"
congruence is in fact *exact* (holds for every ladder length), strengthening the
brief in the corrected residue class.  Sprague (1935) / Grundy (1939) /
Conway (1976): normal‑play P‑positions = Grundy‑`0` positions = `r ≡ 0 (mod m+1)`,
recovered here as `winsN_eq_false_iff`.
-/

open NuclearEscalationMisere






/-
Modulus‑arithmetic crux.  For a positive position `pos` and target residue
`t ∈ {0,1}`: none of the `q-1` legal predecessors is `≡ t (mod q)` iff
`pos ≡ t (mod q)`.
-/

theorem NuclearEscalationMisere.wins_eq_false_iff(m : ℕ) (hm : 1 ≤ m) (r : ℕ) :
    wins m r = false ↔ r % (m + 1) = 1 := by sorry
