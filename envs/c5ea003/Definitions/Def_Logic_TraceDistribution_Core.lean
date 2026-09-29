-- Prove2me | Definitions.Def_Logic_TraceDistribution_Core
-- name    : Logic_TraceDistribution_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:08:31.134625+00:00
-- url     : https://prove2.me/theorems/4e1895ad-639a-41b7-a02a-ffa86a47b60f
-- title:
--   Aether Catalog definitions — Logic_TraceDistribution_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.TraceDistribution.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/TraceDistribution/Core.lean by skeleton subtraction
import Mathlib
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

namespace TraceDistribution

/-! ## Definitions -/

/-- `fixedCard X g = |X^g|`, the number of points of `X` fixed by `g`. -/
noncomputable def fixedCard {G : Type*} [Group G] (X : Type*) [MulAction G X] (g : G) : ℕ :=
  Nat.card (fixedBy X g)

/-- The **trace distribution** of a finite `G`-action: the multiset `{|X^g| : g ∈ G}`,
indexed by the group elements (so its cardinality is always `|G|`). -/
noncomputable def traceDistribution (G : Type*) [Group G] [Fintype G]
    (X : Type*) [MulAction G X] : Multiset ℕ :=
  (Finset.univ : Finset G).val.map (fixedCard X)

/-- `orbitCount G X k` is the number of `G`-orbits on the set `X^k` of `k`-tuples. -/
noncomputable def orbitCount (G : Type*) [Group G] (X : Type*) [MulAction G X] (k : ℕ) : ℕ :=
  Nat.card (Quotient (orbitRel G (Fin k → X)))

/-- The gradewise **q-series** (fixed-point generating polynomial) of the action:
`∑_{g ∈ G} q^{|X^g|} ∈ ℤ[q]`. -/
noncomputable def traceSeries (G : Type*) [Group G] [Fintype G]
    (X : Type*) [MulAction G X] : Polynomial ℤ :=
  ∑ g : G, (Polynomial.X : Polynomial ℤ) ^ (fixedCard X g)

/-! ## Burnside's lemma, graded over tuple length -/


/-- A `k`-tuple is fixed by `g` exactly when each of its entries is: this is the
"tensor power" structure that turns Burnside's lemma into a power-sum statement. -/
def fixedByPiEquiv {G : Type*} [Group G] (X : Type*) [MulAction G X] (g : G) (k : ℕ) :
    fixedBy (Fin k → X) g ≃ (Fin k → fixedBy X g) where
  toFun f i := ⟨f.1 i, by
    have h := f.2
    rw [mem_fixedBy] at h ⊢
    exact congrFun h i⟩
  invFun f := ⟨fun i => (f i).1, by
    rw [mem_fixedBy]; funext i; exact (f i).2⟩
  left_inv f := by ext i; rfl
  right_inv f := by ext i; rfl




/-! ## Elementary structure of the trace distribution -/







/-! ## The main equivalence -/





/-! ## A bound that does not depend on `|X|`

The joint support of the two trace distributions has at most `2·|G|` distinct values,
simply because each distribution has exactly `|G|` entries.  Feeding this into the
*support* form of power-sum rigidity gives a threshold that is independent of the size
of the sets acted on — a genuine improvement whenever a small group acts on a large
set (e.g. `ℤ/2` acting on a million points: `k < 4` already suffices). -/





/-! ## The gradewise q-series form -/




end TraceDistribution


