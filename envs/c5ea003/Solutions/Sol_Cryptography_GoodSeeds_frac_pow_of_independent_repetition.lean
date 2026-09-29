-- Prove2me | solution 1 for Cryptography.GoodSeeds.frac_pow_of_independent_repetition
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:34:33.005928+00:00
-- url     : https://prove2.me/submissions/f61db966-57f2-4b6e-baf6-b4f83bd3a7e6

-- Sol generated from Cryptography/GoodSeeds/Core.lean
import Mathlib
import Definitions.Def_Cryptography_GoodSeeds_Core
import Theorems.Thm_Cryptography_GoodSeeds_mem_goodSeeds

/-!
# Good seeds and the fraction of a finite level set

The catalog already contains a great deal of machinery for randomised
cryptographic arguments: honest-verifier simulators, guarded execution traces,
bounded search for witnesses, and various counting arguments.  What was missing
is the elementary — but ubiquitous — *bookkeeping layer* that turns a cardinality
statement about a finite set of random seeds into a statement about a
**fraction** of the seed space, and, crucially, the decomposition of that
fraction along the **level sets of a cost function**.

This file supplies that layer.

## Main definitions

* `Cryptography.GoodSeeds.goodSeeds Ω acc` — the seeds in a finite seed space
  `Ω` on which the event `acc` occurs.
* `Cryptography.GoodSeeds.frac Ω acc` — the rational fraction
  `|goodSeeds Ω acc| / |Ω|`.
* `Cryptography.GoodSeeds.levelSet Ω cost i` — the seeds of cost exactly `i`.

## Main results

* `frac_nonneg`, `frac_le_one`, `frac_eq_one_iff`, `frac_eq_zero_iff` — the
  fraction is a genuine probability on a nonempty seed space.
* `frac_add_frac_not` — complementation.
* `frac_add_of_disjoint`, `frac_mono` — additivity and monotonicity.
* `sum_card_levelSet`, `sum_frac_levelSet` — **the fractions of the level sets of
  a bounded cost function sum to one**: the missing bookkeeping.
* `frac_sublevel_eq_sum_frac_levelSet` — a sublevel fraction is the partial sum
  of level-set fractions.
* `frac_le_of_markov` — Markov's inequality in level-set form.
* `expCost_eq_sum_level_frac`, `expCost_eq_sum_tail_frac` — the two layer-cake
  identities recovering the average cost from the level-set fractions.
* `frac_pow_of_independent_repetition` — the fraction of seed *vectors* all of
  whose coordinates are good is the `k`-th power of the fraction: soundness
  amplification, exactly.

-- !-- Lab Notes -- !--
Hypothesis (LS1): every "with probability ≥ ε over the seeds" statement in the
catalog can be reduced to a `Finset.card` computation plus a division, and the
resulting operator `frac` is a finitely additive probability measure on the
Boolean algebra of decidable events.
Experiment: define `frac` as a rational quotient of cardinalities and attempt to
derive the measure axioms without any `Nonempty` hypothesis.
Outcome: partially refuted.  Non-negativity, monotonicity in the numerator and
finite additivity hold unconditionally; `frac Ω acc ≤ 1`, `frac Ω (fun _ => True)
= 1` and complementation all *fail* for `Ω = ∅`, because `x / 0 = 0` in Lean's
rationals makes the empty seed space assign measure `0` to the sure event.  Every
normalisation statement below therefore carries an explicit `Ω.Nonempty` guard —
this is the "guarding" discipline the catalog already uses for bounded search,
transplanted to the counting layer.
Analysis: the level-set decomposition `sum_frac_levelSet` is the structural heart:
it is `Finset.card_eq_sum_card_fiberwise` divided by `|Ω|`, and it is what lets
Markov, the sublevel identity and the heavy-row argument of `Rewinding.lean` all
be proved by pure `Finset` manipulation with no measure theory.
Critique: `frac` is *not* a `Measure`; it is a rational-valued finitely additive
functional.  That is deliberate — it keeps every statement decidable and
`decide`-checkable on small cases, which is what a cryptographic soundness bound
needs.
-/

open Cryptography
open GoodSeeds

open Finset

variable {σ : Type*} {Ω : Finset σ}




variable {acc : σ → Prop} [DecidablePred acc]











variable {p q : σ → Prop} [DecidablePred p] [DecidablePred q]





/-! ## Level sets of a cost function

The piece of bookkeeping that the catalog was missing: a finite seed space is
stratified by a cost function (number of oracle queries, search depth, running
time, Hamming weight of an error, …), and the fractions of the strata must add
up to one. -/


variable (cost : σ → ℕ)








/-! ### The layer-cake identities

The average of a bounded cost function is recoverable from the level-set
fractions in two ways: as a weighted sum over the levels, and — the *layer cake*
— as an unweighted sum of the tail fractions.  These are the two identities that
make the level-set bookkeeping actually useful. -/







/-! ## Independent repetition -/



open Cryptography.GoodSeeds in
theorem solution(Ω : Finset σ) (acc : σ → Prop)
    [DecidablePred acc] (k : ℕ) :
    frac (Fintype.piFinset fun _ : Fin k => Ω) (fun f => ∀ i, acc (f i)) = (frac Ω acc) ^ k := by
  classical
  have hset : (Fintype.piFinset fun _ : Fin k => Ω).filter (fun f => ∀ i, acc (f i))
      = Fintype.piFinset fun _ : Fin k => goodSeeds Ω acc := by
    ext f
    simp only [Finset.mem_filter, Fintype.mem_piFinset, mem_goodSeeds]
    exact ⟨fun ⟨h1, h2⟩ i => ⟨h1 i, h2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
  unfold frac goodSeeds
  rw [hset, Fintype.card_piFinset, Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [div_pow]
  simp only [goodSeeds]
  push_cast
  ring
