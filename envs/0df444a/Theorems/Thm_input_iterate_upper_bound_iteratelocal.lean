-- Prove2me | Theorems.Thm_input_iterate_upper_bound_iteratelocal
-- name    : input_iterate_upper_bound_iteratelocal
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-29T06:39:58.395709+00:00
-- url     : https://prove2.me/theorems/54ffed78-76f7-4c88-855a-b232a547d2f0
-- title:
--   Tao 2022, (1.7) plus (1.13): Syracuse iterate upper bound, IterateLocal-namespaced self-contained form
-- statement:
--   Child input node for `syracuse_first_passage_finite_tail_bound` (b179e2a6-29fd-4151-8b97-35fd2e1bb5a1) in the tao-collatz mission. Tao 2022, (1.7) + (1.13): the Syracuse iterate upper bound. From (1.7), $$\\mathrm{Syr}^{n_0}(n) = 3^{n_0} 2^{-|a^{(n_0)}(n)|} n + F_{n_0}(a^{(n_0)}(n)),$$ and (1.13) gives $0 \\le F_{n_0}(a) \\le 3^{n_0}$, whence the displayed bound $$\\mathrm{Syr}^{n_0}(n) \\le \\frac{3^{n_0} n}{2^{|a^{(n_0)}(n)|}} + 3^{n_0}$$ for odd $n$. This is the passage-time input: combined with the high-valuation event, it is what forces the $n_0$-th Syracuse iterate of a window element below $x$, so that the no-first-passage event sits inside the low-valuation (bad) event. This node is the IterateLocal-namespaced self-contained form: the valuation helpers (`syrVal`, `valVec`, `valSum`) are defined inside `namespace IterateLocal` in the preamble using only import-only root identifiers (`syracuseStep` from Definitions.Def_syracuseOrbitMin, `Nat.factorization`, Mathlib), and the statement refers to them by qualified name, so no submission-side redefinition can collide. Formalization note: the valuation-vector sum is the explicit `Finset.sum Finset.univ` with no scoped notation; every valuation lambda carries its explicit `Fin n₀` domain.

import Mathlib
import Definitions.Def_syracuseOrbitMin

noncomputable section


attribute [instance] Classical.propDecidable

namespace IterateLocal

/-- The 2-adic valuation of `3n+1` (Tao 2022, section 1.2). -/
def syrVal (n : ℕ) : ℕ := Nat.factorization (3 * n + 1) 2

/-- The Syracuse valuation vector of length `n₀` (Tao 2022, (1.8)). -/
def valVec (n₀ : ℕ) (n : ℕ) : Fin n₀ → ℕ := fun j => syrVal (syracuseStep^[j.val] n)

/-- The valuation-vector sum (Tao 2022, (1.4)). -/
def valSum (n₀ n : ℕ) : ℕ := Finset.sum Finset.univ (fun j => valVec n₀ n j)

end IterateLocal

theorem input_iterate_upper_bound_iteratelocal :
    ∀ n₀ n : ℕ, Odd n →
      ((syracuseStep^[n₀] n : ℕ) : ℝ)
        ≤ (3 : ℝ) ^ n₀ * n / (2 : ℝ) ^ (IterateLocal.valSum n₀ n) + (3 : ℝ) ^ n₀ := by sorry
