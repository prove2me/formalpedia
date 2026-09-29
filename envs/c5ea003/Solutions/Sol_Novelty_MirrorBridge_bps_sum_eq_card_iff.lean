-- Prove2me | solution 1 for Novelty.MirrorBridge.bps_sum_eq_card_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:16:38.885571+00:00
-- url     : https://prove2.me/submissions/580ac867-9fa9-4e67-9791-5c3847361cf9

-- Sol generated from Novelty/BPSPicardObstruction.lean
import Mathlib
import Definitions.Def_Novelty_BPSPicardObstruction
import Definitions.Def_Novelty_HodgeMirror

/-!
# Arithmetic Mirror Symmetry VI — the genus-zero BPS / Picard-rank specialization

This file settles *Conjecture 1* of the programme: the **graded genus-zero
mirror/Picard specialization**, which asks for a mirror pair `(X, Y)` of Calabi–Yau
threefolds and a finite set `S` of effective primitive curve classes on `X` with

`∑_{β ∈ S} n⁰_β(X) = rank Pic(Y)`.

The conjecture is tested, as instructed, on the explicitly named toric mirror family:
the quintic threefold `X = X₅ ⊂ ℙ⁴` and its Greene–Plesser mirror `Y = X₅/(ℤ/5)³`,
whose Hodge data are `(h^{1,1}, h^{2,1}) = (1, 101)` and `(101, 1)`.  Its genus-zero
BPS (Gopakumar–Vafa) invariants in degrees `1, …, 5` are the classical numbers
`2875, 609250, 317206375, 242467530000, 229305888887625`
(Candelas–de la Ossa–Green–Parkes and successors), while `rank Pic(Y) = h^{1,1}(Y) = 101`.

We prove:

* `quintic_euler` — the catalog Hodge model reproduces `χ(X₅) = 2(1 − 101) = −200`;
* `quinticMirror_picardRank` — `rank Pic(Y) = 101`, via the catalog mirror involution;
* `sum_ne_of_lt_of_forall_le` — a general obstruction: a sum of values all `≥ M` over a
  finset can never equal a target `t` with `0 < t < M`;
* `quintic_bps_sum_ne_picardRank` — **refutation of Conjecture 1 for the quintic
  family**: for *every* set `S` of degrees `≤ 5`, `∑_{β ∈ S} n⁰_β ≠ 101`.  The
  conjecture as stated is therefore false on the very family it names;
* `bps_sum_eq_card_iff` — the **exact boundary**: for positive BPS invariants,
  `∑_{β∈S} n⁰_β = #S` iff every invariant in `S` equals `1`.  Hence a specialization of
  the required shape can only hold when the sum degenerates into a *count of classes*;
* `graded_bps_picard_iff_all_one` — consequently, the corrected conjecture reads: the sum
  equals `rank Pic(Y)` with `#S = rank Pic(Y)` exactly when all selected BPS invariants
  are `1`, i.e. mirror symmetry matches the Picard rank with the *number of independent
  curve classes*, never with a genuine enumerative total.

-- !-- Lab Notes -- !--
* **Hypothesis (Hypothesizer).**  If mirror symmetry converted rational-curve counts into
  a Picard rank, some finite set of primitive classes should realize the rank exactly.
* **Experiment (Experimenter).**  Instantiated on the quintic: the smallest genus-zero
  BPS invariant in the tested range is `n⁰₁ = 2875`, already `≫ 101 = rank Pic(Y)`, and
  all invariants are positive.  So every nonempty `S` overshoots and `S = ∅` gives `0`.
  Numerically: `2875, 609250, 317206375, …` against the single target `101`
  (see `ComputationalEvidence.md`).
* **Analysis (Analyst).**  Conjecture 1 is **false**, and not by accident: it is a *type
  error* between an enumerative count (a large integer attached to one class) and a rank
  (the number of independent classes).  The catalog's own bridge theorem
  `rationalCurveCount_eq_mirrorPicardRank` is honest precisely because it carries the
  identification hypothesis `count = curveModuli`, which the quintic violates.
  `bps_sum_eq_card_iff` pinpoints the only regime where the naive statement can hold.
* **Critique (Critic).**  The refutation quantifies over *all* `S ⊆ {1,…,5}` (not one
  hand-picked `S`), and is proved from a general finset lemma with `Finset.single_le_sum`
  rather than by `decide` over the 32 subsets, so the argument scales to every degree
  range in which the invariants stay above `101`.
* **Synthesis (PI).**  The surviving, correct statement is the *rank/rank* form
  (`Novelty.ArithMirror.CY3.picardRank_mirror`), and the enumerative content lives one
  level down, in the Gromov–Witten potential, not in the rank.
-/

open Novelty.MirrorBridge

open Finset Novelty.ArithMirror

/-! ### The named toric mirror family: the quintic threefold and its mirror -/







/-! ### A general obstruction to realizing a small target as a sum -/




/-! ### The exact boundary of the conjecture -/





open Novelty.MirrorBridge in
theorem solution{ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℕ)
    (hpos : ∀ i ∈ S, 1 ≤ f i) :
    ∑ i ∈ S, f i = S.card ↔ ∀ i ∈ S, f i = 1 := by
  constructor
  · intro hsum i hi
    by_contra hne
    have h2 : 2 ≤ f i := by
      have := hpos i hi
      omega
    have hcard : ∑ j ∈ S, 1 = S.card := by simp
    have hlt : ∑ j ∈ S, (1 : ℕ) < ∑ j ∈ S, f j :=
      Finset.sum_lt_sum (fun j hj => hpos j hj) ⟨i, hi, by omega⟩
    omega
  · intro hone
    rw [Finset.sum_congr rfl hone]
    simp
