-- Prove2me | Theorems.Thm_TraceDistribution_traceDistribution_eq_of_card_orbits_eq
-- name    : TraceDistribution.traceDistribution_eq_of_card_orbits_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:57:15.898639+00:00
-- url     : https://prove2.me/theorems/d5f80f03-f7d6-4ed2-995d-6319543072d8
-- title:
--   The hard direction: agreement of the orbit counts on `k`-tuples for the finitely
-- statement:
--   The hard direction: agreement of the orbit counts on `k`-tuples for the finitely
--   many `k ≤ max |X| |Y|` already forces the two trace distributions to coincide.
--
--   The proof feeds graded Burnside into the interpolation-duality rigidity theorem
--   `multiset_eq_of_powerSum_eq`.
--
--   ```lean
--   theorem TraceDistribution.traceDistribution_eq_of_card_orbits_eq{G : Type*} [Group G] [Fintype G]
--       (X Y : Type*) [MulAction G X] [MulAction G Y] [Finite X] [Finite Y]
--       (h : ∀ k ≤ max (Nat.card X) (Nat.card Y), orbitCount G X k = orbitCount G Y k) :
--       traceDistribution G X = traceDistribution G Y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/TraceDistribution/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/TraceDistribution/Core.lean#L170

-- Thm stub generated from Logic/TraceDistribution/Core.lean
import Mathlib
import Definitions.Def_Logic_TraceDistribution_Core
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






/-! ## Elementary structure of the trace distribution -/







/-! ## The main equivalence -/

theorem TraceDistribution.traceDistribution_eq_of_card_orbits_eq{G : Type*} [Group G] [Fintype G]
    (X Y : Type*) [MulAction G X] [MulAction G Y] [Finite X] [Finite Y]
    (h : ∀ k ≤ max (Nat.card X) (Nat.card Y), orbitCount G X k = orbitCount G Y k) :
    traceDistribution G X = traceDistribution G Y := by sorry
