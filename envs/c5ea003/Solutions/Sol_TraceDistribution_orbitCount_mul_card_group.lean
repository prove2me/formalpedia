-- Prove2me | solution 1 for TraceDistribution.orbitCount_mul_card_group
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T19:24:02.482766+00:00
-- url     : https://prove2.me/submissions/6781ab3a-3010-446d-ac77-f5d5d2d6c185

-- Sol generated from Logic/TraceDistribution/Core.lean
import Mathlib
import Definitions.Def_Logic_TraceDistribution_Core
import Theorems.Thm_TraceDistribution_powerSum_traceDistribution
/-
# Conjecture A, closed: trace distributions of finite group actions

Let `G` be a finite group acting on a finite set `X`.  Two invariants compete for the
role of "the" combinatorial shadow of the action:

* the **trace distribution** `traceDistribution G X = {| X^g | : g ∈ G}`, the multiset
  of fixed-point counts (equivalently, the permutation character of the action, taken
  as an unordered multiset rather than as a class function);
* the **orbit spectrum** `k ↦ orbitCount G X k`, the number of `G`-orbits on the set
  `X^k` of `k`-tuples (`Fin k → X`).

The main results of this file prove that the two invariants are *equivalent*, and that
the equivalence is already witnessed by a finite, explicitly bounded, range of `k`:

* `orbitCount_mul_card_group` — Burnside's lemma in the graded form
  `|orbits on X^k| · |G| = ∑_{g ∈ G} |X^g|^k`, i.e. the orbit spectrum is exactly the
  sequence of **power sums** of the trace distribution.
* `traceDistribution_eq_iff_card_orbits_eq` — **the main theorem.** Two actions have
  the same trace distribution **iff** they have the same orbit counts on `k`-tuples
  for all `k ≤ max (|X|) (|Y|)`.
* `card_orbits_eq_of_le` — the finite range of `k` already forces agreement for
  *every* `k`: the orbit spectrum is a *rigid* sequence.
* `traceDistribution_graded_eq` — the gradewise q-series form: the fixed-point
  generating polynomial `∑_{g ∈ G} q^{|X^g|} ∈ ℤ[q]` is a complete invariant, and it
  agrees for `X` and `Y` iff the finitely many orbit counts do.

The bridge from "equal power sums" to "equal multisets" is `multiset_eq_of_powerSum_eq`,
proved in `Logic.TraceDistribution.PowerSums` by Lagrange-interpolation duality.

## Lab notes (experimental data)

* `G = ℤ/2` acting on `X = ℤ/2` by translation: `traceDistribution = {2, 0}`,
  orbit counts `1, 1, 2, 4, 8, …` (`= (2^k + 0^k)/2`).
* `G = ℤ/2` acting trivially on a 1-point set `Y`: `traceDistribution = {1, 1}`,
  orbit counts `1, 1, 1, 1, …`.  The two are separated already at `k = 2`
  (`2 ≠ 1`), well inside the bound `max(2,1) = 2`.
* The bound is *not* vacuous: `k = 0` always gives `orbitCount = 1` for both actions
  and `k = 1` gives the plain orbit count, so genuinely higher `k` is needed.
-/

open MulAction Finset

open TraceDistribution

/-! ## Definitions -/





/-! ## Burnside's lemma, graded over tuple length -/

/-- Burnside's lemma in `Nat.card` form. -/
theorem burnside (G : Type*) [Group G] [Fintype G] (β : Type*) [MulAction G β] [Finite β] :
    ∑ g : G, fixedCard β g = Nat.card (Quotient (orbitRel G β)) * Nat.card G := by
  classical
  have _ := Fintype.ofFinite β
  have _ := Fintype.ofFinite (Quotient (orbitRel G β))
  simp only [fixedCard, Nat.card_eq_fintype_card]
  exact MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G β


/-- `|(X^k)^g| = |X^g|^k`. -/
theorem fixedCard_pi {G : Type*} [Group G] (X : Type*) [MulAction G X] [Finite X]
    (g : G) (k : ℕ) : fixedCard (Fin k → X) g = (fixedCard X g) ^ k := by
  unfold fixedCard
  rw [Nat.card_congr (fixedByPiEquiv X g k)]
  simp [Nat.card_pi]



/-! ## Elementary structure of the trace distribution -/







/-! ## The main equivalence -/





/-! ## A bound that does not depend on `|X|`

The joint support of the two trace distributions has at most `2·|G|` distinct values,
simply because each distribution has exactly `|G|` entries.  Feeding this into the
*support* form of power-sum rigidity gives a threshold that is independent of the size
of the sets acted on — a genuine improvement whenever a small group acts on a large
set (e.g. `ℤ/2` acting on a million points: `k < 4` already suffices). -/





/-! ## The gradewise q-series form -/





open TraceDistribution in
theorem solution(G : Type*) [Group G] [Fintype G]
    (X : Type*) [MulAction G X] [Finite X] (k : ℕ) :
    orbitCount G X k * Nat.card G
      = (Multiset.map (fun a => a ^ k) (traceDistribution G X)).sum := by
  rw [powerSum_traceDistribution, orbitCount, ← burnside G (Fin k → X)]
  refine Finset.sum_congr rfl fun g _ => ?_
  exact fixedCard_pi (G := G) X g k
