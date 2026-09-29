-- Prove2me | Definitions.Def_Probability_WignerUniversalOddMoments
-- name    : Probability_WignerUniversalOddMoments
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T18:00:55.447688+00:00
-- url     : https://prove2.me/theorems/3a44e72c-e6ed-4670-b889-649d041ad8e1
-- title:
--   Aether Catalog definitions — Probability_WignerUniversalOddMoments
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.WignerUniversalOddMoments`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/WignerUniversalOddMoments.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_WignerAllOrderParity
import Definitions.Def_Probability_WignerMomentGrowth
import Definitions.Def_Probability_WignerSecondMomentConcentration
import Definitions.Def_Probability_WignerUniversalFourthMoment
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Universality at all orders: the walk–moment formula, tightness, and vanishing odd moments

`Probability.WignerUniversalFourthMoment` proves universality of the spectral
moments of a general Wigner ensemble (arbitrary finitely supported, centred,
unit-variance entry law) up to order four, and
`Probability.WignerAllOrderParity` handles all orders for the Rademacher ensemble.
This file removes both restrictions at once, for the two statements that do not
require the Catalan bookkeeping:

* `WignerUniversal.gexpect_walk_prod` — the **walk–moment formula**: for a loop-free
  family of steps, the ensemble average of the walk monomial is the product, over
  edges, of the entry-law moment of order equal to the multiplicity of that edge.
  Independence enters exactly once, through `gexpect_prod`.

* `WignerUniversal.gexpect_walk_prod_eq_zero_of_edgeMult_one` — a walk traversing
  some edge exactly once averages to `0`, because the entry law is centred.  This is
  the general-law replacement for the sign-flip involution of the Rademacher case.

* `WignerUniversal.gexpect_trace_pow_bound` — combining the vanishing with the
  spanning-tree counting of `Probability.WignerMomentGrowth`: a walk contributing to
  `E [tr (W^(m+1))]` uses no edge just once, hence visits at most `k+1` vertices
  whenever `m ≤ 2k`, and therefore

    `|E [tr (W^(m+1))]| ≤ N^(k+1) (k+1)^(m+1) B^(m+1)`,

  where `B` bounds the support of the entry law.

* `WignerUniversal.gexpect_normalizedMoment_even_le` — hence all even normalised
  moments are bounded uniformly in `N` (tightness), and

* `WignerUniversal.tendsto_gexpect_normalizedMoment_odd` — every **odd** normalised
  moment tends to `0` like `N^{-1/2}`, matching the vanishing odd moments of the
  semicircle law, for *every* entry law and at *every* odd order.
-/

open Matrix BigOperators Finset Filter Topology
open RademacherWigner (edgeOf edgeMult)

namespace WignerUniversal

variable {S : Type*} [Fintype S] {N : ℕ}

/-! ### A crude bound on the support of the entry law -/

/-- A bound for the values taken by the entry law. -/
noncomputable def EntryLaw.vBound (L : EntryLaw S) : ℝ := ∑ s, |L.v s|




/-! ### The walk–moment formula -/

variable {ι : Type*} [Fintype ι]





/-! ### The trace moments of a general Wigner ensemble -/


/-- The walks that can contribute to a trace moment: loop-free, and with no edge
traversed exactly once. -/
def Contributing (m : ℕ) (x : Fin N × (Fin m → Fin N)) : Prop :=
  (∀ t : Fin (m + 1), (Fin.cons x.1 x.2 : Fin (m + 1) → Fin N) t
      ≠ (Fin.snoc x.2 x.1 : Fin (m + 1) → Fin N) t) ∧
  (∀ p, edgeMult (Fin.cons x.1 x.2 : Fin (m + 1) → Fin N)
      (Fin.snoc x.2 x.1 : Fin (m + 1) → Fin N) p ≠ 1)


/-! ### Consequences for the normalised spectral moments -/





end WignerUniversal


