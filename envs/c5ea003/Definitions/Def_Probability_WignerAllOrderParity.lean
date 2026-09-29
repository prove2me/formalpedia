-- Prove2me | Definitions.Def_Probability_WignerAllOrderParity
-- name    : Probability_WignerAllOrderParity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:45:57.247964+00:00
-- url     : https://prove2.me/theorems/4b4c8673-fa1e-42ec-a0de-e0e2c788f679
-- title:
--   Aether Catalog definitions — Probability_WignerAllOrderParity
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.WignerAllOrderParity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/WignerAllOrderParity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerWalkParity
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# All-order walk expansion of the trace, and the exact vanishing of every odd moment

The files `Probability.WignerRademacherEnsemble` and `Probability.WignerWalkParity`
compute the spectral moments of the symmetric Rademacher ensemble at orders `2`, `3`
and `4`, and isolate the sign-flip involution for a walk of fixed length.  This file
removes the length restriction completely:

* `RademacherWigner.trace_pow_succ_sum_walks` expands `tr (M ^ (m+1))` for an
  *arbitrary* matrix as a sum over closed `(m+1)`-walks, encoded as a starting
  vertex `i` together with the remaining vertices `v : Fin m → Fin N`; the `t`-th
  step goes from `(Fin.cons i v) t` to `(Fin.snoc v i) t`.  This is proved by
  induction from the entrywise path expansion `RademacherWigner.pow_apply_sum_walks`.

* The sign-flip calculus is then developed for an arbitrary finite family of steps
  `a b : ι → Fin N` (`edgeMult`, `prod_entry_flipEdge_family`), giving

  - `expect_prod_entry_family_eq_zero_of_card_odd`: **any** odd-size family of steps
    has vanishing ensemble average, and
  - `prod_entry_eq_one_of_even`: a loop-free family all of whose edge multiplicities
    are even has monomial identically `1`,

  hence the exact dichotomy `expect_prod_entry_family`: the ensemble average of a
  walk monomial is `1` if the walk is loop-free with all edge multiplicities even,
  and `0` otherwise.

* Consequently `expect_trace_pow_eq_sum_indicator` reduces the computation of *every*
  moment `E [tr W^m]` to a purely combinatorial count of even closed walks, and
  `expect_trace_pow_odd` proves that **all odd trace moments vanish exactly, at every
  finite dimension `N` and every odd order** — no asymptotics, no error terms.
  Normalising, `expect_normalizedMoment_odd` matches the odd moments of the
  semicircle law (`WignerUniversal`-style statement at all orders, rather than only
  at order `3`).
-/

open Matrix BigOperators Finset

namespace RademacherWigner

variable {N : ℕ}

/-! ### Walk expansion of powers and traces of an arbitrary matrix -/



/-! ### The sign-flip calculus for an arbitrary finite family of steps -/

variable {ι : Type*} [Fintype ι]

/-- The number of steps of the family `(a, b)` that traverse the edge `p`. -/
def edgeMult (a b : ι → Fin N) (p : Fin N × Fin N) : ℕ :=
  (Finset.univ.filter fun t => edgeOf (a t) (b t) = p).card








/-! ### Consequences for the spectral moments -/

/-- A closed `(m+1)`-walk based at `i` with intermediate vertices `v` is *even* if it
never stays put and traverses every edge an even number of times.  These are exactly
the walks that survive the ensemble average. -/
def IsEvenWalk (m : ℕ) (i : Fin N) (v : Fin m → Fin N) : Prop :=
  (∀ t : Fin (m + 1), (Fin.cons i v : Fin (m + 1) → Fin N) t
      ≠ (Fin.snoc v i : Fin (m + 1) → Fin N) t) ∧
  (∀ p, Even (edgeMult (Fin.cons i v : Fin (m + 1) → Fin N)
      (Fin.snoc v i : Fin (m + 1) → Fin N) p))

instance IsEvenWalk.decidablePred {m : ℕ} (i : Fin N) (v : Fin m → Fin N) :
    Decidable (IsEvenWalk m i v) := by
  unfold IsEvenWalk
  infer_instance




end RademacherWigner


