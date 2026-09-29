-- Prove2me | solution 1 for SumsOfMSquares.hasInfSignChanges_univ_of_partialSum_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:52:10.852537+00:00
-- url     : https://prove2.me/submissions/97826a44-1833-4af1-af23-068e7bbfa7bd

-- Sol generated from Novelty/SymPowerSignChangesSumsOfSquares.lean
import Mathlib
import Definitions.Def_Novelty_SumsOfMSquaresSet
import Definitions.Def_Novelty_SymPowerSignChangesSumsOfSquares
/-
# Infinitely many sign changes over sums of `m` squares, for all even `m ≥ 2`

Let `f` be a normalised Hecke eigenform of even weight `k ≥ 2` for `SL(2,ℤ)`, let
`j ≥ 1`, and let `λ_{sym^j f}(n)` be the (real) Dirichlet coefficients of the
`j`-th symmetric-power `L`-function.  A theorem in the literature establishes that
these coefficients exhibit **infinitely many sign changes as `n` ranges over sums
of `m` squares** for `2 ≤ m ≤ 12`.  This file isolates the *structural core* that
lifts such a statement to **all even `m ≥ 2`** (indeed to all `m ≥ 2`), together
with a self-contained analytic oscillation engine.

The arithmetic function `λ_{sym^j f}` is modelled abstractly as an arbitrary real
sequence `a : ℕ → ℝ`.  The sampling sets are the `setOfSumOfMSquares m` from
`SumsOfMSquaresSet.lean`.

Main results:

* `HasInfSignChangesOn` — the sign-change predicate: both the positive and the
  negative sub-samples are infinite.
* `HasInfSignChangesOn.mono` — sign changes propagate to any larger sampling set.
* `hasInfSignChanges_sumOfMSquares_of_two` — **the reduction**: sign changes over
  sums of two squares already force sign changes over sums of `m` squares for every
  `m ≥ 2`, because `S 2 ⊆ S m`.  Thus the whole "extend to all even `m ≥ 2`"
  problem collapses to the single base case `m = 2`.
* `symPower_infSignChanges_even_m` — the mission statement: for all even `m ≥ 2`,
  given the `m = 2` sign-change input, the coefficients change sign infinitely
  often over sums of `m` squares.
* `hasInfSignChanges_sumOfMSquares_iff_univ` — **the collapse**: for `m ≥ 4`,
  sign changes over sums of `m` squares are *equivalent* to unrestricted sign
  changes, since every natural is a sum of `m` squares.
* `hasInfSignChanges_univ_of_partialSum_unbounded` — a Landau-flavoured engine:
  if the partial sums `∑_{n<X} a n` are unbounded above and below, then `a` is
  positive infinitely often and negative infinitely often.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the papers prove the sign-change phenomenon case by
case for small `m`, suggesting `m` genuinely matters.  Bold counter-conjecture:
`m` almost does *not* matter.  Because the sets of sums of squares are nested,
`S 2 ⊆ S 3 ⊆ ...`, a single hard case (`m = 2`) should imply *all* larger `m`,
and from `m = 4` on the sampling set is all of `ℕ`.

Experiment (Experimenter): `HasInfSignChangesOn.mono` (via `Set.Infinite.mono`)
plus `setOfSumOfMSquares_subset` yields the reduction `S 2 ⇒ S m` for `m ≥ 2`.
`setOfSumOfMSquares_eq_univ` (Lagrange) yields the `m ≥ 4` equivalence with the
unrestricted problem.  Independently, an elementary "Filter.eventually one-signed ⇒
partial sums bounded on that side" argument (`by_contra` + `Finset.sum_Ico` split)
proves the oscillation engine.

Analysis (Analyst): the case analysis in the source is an artefact of the analytic
*method* (which produces the `m = 2` input), not of the *conclusion*.  Logically
the extension is free once the base case is in hand.  The genuinely sparse regime
is `m = 2`; `m = 3` is mildly restricted (`n ≢ 7 mod 8`); `m ≥ 4` is unrestricted.

Critique (Critic): is the reduction cheating by hiding the analysis in a
hypothesis?  No — the reduction is a real theorem about the *conclusion shape*,
and we do not assume the conclusion for `m`; we assume only the strictly weaker
`m = 2` instance and derive all larger `m`.  The `Even m` hypothesis is retained
to match the mission scope but is not needed (the result holds for all `m ≥ 2`);
this is documented.  The oscillation engine is fully self-contained and uses
`by_contra`, a partial-sum split, and a boundedness argument — not `decide`.

Synthesis (PI): "all even `m ≥ 2`" is not harder than "`m = 2`"; the difficulty
is entirely concentrated in the two-square case, and evaporates for `m ≥ 4`.
-/

open SumsOfMSquares

open Finset








open SumsOfMSquares in
theorem solution{a : ℕ → ℝ}
    (hpos : ∀ C : ℝ, ∃ X, C < ∑ n ∈ Finset.range X, a n)
    (hneg : ∀ C : ℝ, ∃ X, (∑ n ∈ Finset.range X, a n) < C) :
    HasInfSignChangesOn a Set.univ := by
      constructor <;> contrapose! hneg
      · -- only finitely many positive terms ⇒ partial sums bounded above
        obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, a n ≤ 0 :=
          ⟨hneg.bddAbove.some + 1, fun n hn => not_lt.1 fun contra =>
            not_lt_of_ge (hneg.bddAbove.choose_spec ⟨Set.mem_univ _, contra⟩) hn⟩
        set B := ∑ n ∈ Finset.range N, |a n| with hB_def
        have hB : ∀ X, ∑ n ∈ Finset.range X, a n ≤ B := by
          intro X; by_cases hX : X ≤ N <;> simp_all +decide
          · exact le_trans (Finset.sum_le_sum fun _ _ => le_abs_self _)
              (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hX) fun _ _ _ => abs_nonneg _)
          · rw [← Finset.sum_range_add_sum_Ico _ hX.le]
            exact add_le_of_nonpos_right (Finset.sum_nonpos fun n hn => hN n <| Finset.mem_Ico.mp hn |>.1)
              |> le_trans <| Finset.sum_le_sum fun n hn => le_abs_self _
        exact absurd (hpos B) (by push_neg; tauto)
      · -- only finitely many negative terms ⇒ partial sums bounded below
        obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, 0 ≤ a n :=
          ⟨hneg.bddAbove.some + 1, fun n hn => not_lt.1 fun contra =>
            not_lt_of_ge (hneg.bddAbove.choose_spec ⟨Set.mem_univ _, contra⟩) hn⟩
        use ∑ n ∈ Finset.range N, min (a n) 0
        intro X; cases le_total X N <;> simp_all +decide
        · rw [← Finset.sum_range_add_sum_Ico _ ‹X ≤ N›]
          exact add_le_of_nonpos_right (Finset.sum_nonpos fun n hn => min_le_right _ _)
            |> le_trans <| Finset.sum_le_sum fun n hn => min_le_left _ _
        · rw [← Finset.sum_range_add_sum_Ico _ ‹N ≤ X›]
          exact le_add_of_le_of_nonneg (Finset.sum_le_sum fun _ _ => min_le_left _ _)
            (Finset.sum_nonneg fun _ _ => hN _ <| Finset.mem_Ico.mp ‹_› |>.1)
