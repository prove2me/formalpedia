-- Prove2me | Theorems.Thm_RademacherWigner_trace_pow_succ_sum_walks
-- name    : RademacherWigner.trace_pow_succ_sum_walks
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:03:05.615065+00:00
-- url     : https://prove2.me/theorems/3ee44d7e-72bf-4246-85a5-256e44fc06d5
-- title:
--   Closed-walk expansion of the trace of a power.
-- statement:
--   **Closed-walk expansion of the trace of a power.**  `tr (M ^ (m+1))` is the sum
--   over closed `(m+1)`-walks: a base point `i` and `m` further vertices `v`.
--
--   ```lean
--   theorem RademacherWigner.trace_pow_succ_sum_walks(M : Matrix (Fin N) (Fin N) ℝ) (m : ℕ) :
--       (M ^ (m + 1)).trace = ∑ i : Fin N, ∑ v : Fin m → Fin N, ∏ t : Fin (m + 1),
--         M ((Fin.cons i v : Fin (m + 1) → Fin N) t)
--           ((Fin.snoc v i : Fin (m + 1) → Fin N) t) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerAllOrderParity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerAllOrderParity.lean#L97

-- Thm stub generated from Probability/WignerAllOrderParity.lean
import Mathlib
import Definitions.Def_Probability_WignerAllOrderParity
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

theorem RademacherWigner.trace_pow_succ_sum_walks(M : Matrix (Fin N) (Fin N) ℝ) (m : ℕ) :
    (M ^ (m + 1)).trace = ∑ i : Fin N, ∑ v : Fin m → Fin N, ∏ t : Fin (m + 1),
      M ((Fin.cons i v : Fin (m + 1) → Fin N) t)
        ((Fin.snoc v i : Fin (m + 1) → Fin N) t) := by sorry
