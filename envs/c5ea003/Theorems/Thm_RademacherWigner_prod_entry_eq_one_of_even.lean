-- Prove2me | Theorems.Thm_RademacherWigner_prod_entry_eq_one_of_even
-- name    : RademacherWigner.prod_entry_eq_one_of_even
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:02:41.982016+00:00
-- url     : https://prove2.me/theorems/77382465-c3f5-4fb8-ba76-264ed1b2c0c4
-- title:
--   A loop-free family all of whose edge multiplicities are even has monomial
-- statement:
--   A loop-free family all of whose edge multiplicities are even has monomial
--   identically `1`: every Rademacher variable occurs to an even power.
--
--   ```lean
--   theorem RademacherWigner.prod_entry_eq_one_of_even(g : Config N) (a b : ι → Fin N)
--       (hne : ∀ t, a t ≠ b t) (heven : ∀ p, Even (edgeMult a b p)) :
--       (∏ t, entry g (a t) (b t)) = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerAllOrderParity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerAllOrderParity.lean#L177

-- Thm stub generated from Probability/WignerAllOrderParity.lean
import Mathlib
import Definitions.Def_Probability_WignerAllOrderParity
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

open RademacherWigner

variable {N : ℕ}

/-! ### Walk expansion of powers and traces of an arbitrary matrix -/



/-! ### The sign-flip calculus for an arbitrary finite family of steps -/

variable {ι : Type*} [Fintype ι]

theorem RademacherWigner.prod_entry_eq_one_of_even(g : Config N) (a b : ι → Fin N)
    (hne : ∀ t, a t ≠ b t) (heven : ∀ p, Even (edgeMult a b p)) :
    (∏ t, entry g (a t) (b t)) = 1 := by sorry
