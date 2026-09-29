-- Prove2me | solution 1 for ZnGainSharp.parallelEdges_gainable_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:19:11.963722+00:00
-- url     : https://prove2.me/submissions/87499c43-c32c-48f3-b098-5bc1308962f7

-- Sol generated from Novelty/ZnGainSharp.lean
import Mathlib
import Definitions.Def_Novelty_ZnGainSharp
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

/-!
# Sharpness of the `(n+1)K₂` excluded minor for `ℤ/n`-gainability

This companion file to `ZnGain.lean` proves that the excluded minor `(n+1)K₂` for the
parallel-class family is **sharp**: `kK₂` (the `k`-fold parallel class) is `ℤ/n`-gainable
**iff** `k ≤ n`.  Hence `nK₂` *is* gainable while `(n+1)K₂` is the *minimal* non-gainable
parallel class — exactly the threshold predicted by the Zaslavsky/Funk conjecture.

The minimal gain framework (`signedSum`, `BiasedGraph`, `Gainable`, `parallelEdges`) is
restated here under the namespace `ZnGainSharp` so that this file is independently
verifiable; it mirrors the development in `ZnGain.lean`.

## Main results

* `parallelEdges_gainable_iff` — `kK₂` is `ℤ/n`-gainable iff `k ≤ n` (the *exact* threshold).
* `parallelEdges_gainable` — `nK₂` is `ℤ/n`-gainable (lower edge of the threshold).
* `parallelEdges_succ_not_gainable` — `(n+1)K₂` is *not* `ℤ/n`-gainable (the excluded minor).
* `signed_three_parallel_not_gainable` — the `n = 2` (signed-graph) instance: `3K₂` is not
  `ℤ/2`-gainable, matching the first excluded minor `3K₂ = (2+1)K₂` of the signed case.

## References

* T. Zaslavsky, *Biased graphs. I*, JCTB 1989.
* D. Funk, *Biased graphs and their excluded minors*, 2015.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).
  H4 (bold): the excluded minor `(n+1)K₂` is *sharp* — `nK₂` should be exactly realisable
     in `ℤ/n` by the labelling `i ↦ i`, and no parallel class with more than `n` edges can
     be realised.  Thus `kK₂` gainable ⇔ `k ≤ n`.
  H5: specialising to `n = 2` recovers the signed-graph threshold `3K₂`.

EXPERIMENT (Experimenter).
  - Forward (`gainable ⇒ k ≤ n`): a realisation forces the labels of distinct parallel
    edges to differ (an unbalanced digon has nonzero gain `g i − g j`), so `g` is injective
    `Fin k ↪ ℤ/n`, giving `k ≤ n` by `Fintype.card_le_of_injective` and `ZMod.card`.
  - Backward (`k ≤ n ⇒ gainable`): pick an injective `g : Fin k → ℤ/n` (exists since
    `k ≤ |ℤ/n|`); every digon is unbalanced and has gain `g i − g j ≠ 0`.  PROVED.
  - `n = 2`: instance of `parallelEdges_succ_not_gainable` at `n = 2`.  PROVED.

ANALYSIS (Analyst).
  Sharpness shows the cycle-only abstraction already sees the *entire* parallel-class slice
  of the conjecture, threshold included.  The remaining gap to the full conjecture
  (`±K₃`, `−K₄`) is precisely the structure invisible to digons.

CRITIQUE (Critic).
  - `parallelEdges_gainable_iff` is a genuine `↔` whose two directions use different ideas
    (pigeonhole vs. explicit construction); not `decide`-able since `n` is universally
    quantified.
  - No hypothesis is idle: `[NeZero n]` is exactly what powers `ZMod.card`.

SYNTHESIS (PI).
  Together with `ZnGain.lean`, this pins the parallel-class excluded minor to *exactly*
  `(n+1)K₂` for every `n ≥ 1`, with `nK₂` realisable — the sharp form of the threshold.
-/

open scoped BigOperators

open ZnGainSharp





/-
**Sharpness of the threshold.** `kK₂` is `ℤ/n`-gainable if and only if `k ≤ n`.
-/





open ZnGainSharp in
theorem solution(k n : ℕ) [NeZero n] :
    Gainable n (parallelEdges k) ↔ k ≤ n := by
  constructor;
  · intro h
    obtain ⟨g, hg⟩ := h
    have h_inj : Function.Injective g := by
      intro i j hij; specialize hg [ ( i, Bool.true ), ( j, Bool.false ) ] ; simp_all +decide [ parallelEdges ] ;
      simp_all +decide [ signedSum ]
    have h_card : k ≤ n := by
      have := Fintype.card_le_of_injective g h_inj; simp_all +decide [ ZMod.card ] ;
    exact h_card;
  · intro hk
    obtain ⟨g, hg⟩ : ∃ g : Fin k → ZMod n, Function.Injective g := by
      obtain ⟨g, hg⟩ : ∃ g : Fin k ↪ ZMod n, True := by
        exact ⟨ ( Function.Embedding.nonempty_of_card_le <| by simpa [ ZMod.card ] using hk ) |> Classical.choice, trivial ⟩;
      exact ⟨ g, g.injective ⟩;
    use g;
    rintro c ⟨ i, j, hij, rfl ⟩ ; simp +decide [ signedSum ] ;
    exact iff_of_false ( by tauto ) ( by rw [ add_eq_zero_iff_eq_neg ] ; exact fun h => hij <| hg <| by aesop )
