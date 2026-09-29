-- Prove2me | Definitions.Def_LinearOptimization_PathFollowing
-- name    : LinearOptimization_PathFollowing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-06T14:45:33.847567+00:00
-- url     : https://prove2.me/theorems/e77f7533-5532-491f-b305-3361bc9172d6
-- title:
--   Primal path following algorithm
-- statement:
--   **(The primal path following algorithm, boxed, pp. 425-426, as an iteration predicate)**
--
--   Inputs (p. 425):
--
--   - **(a)** the data (A, b, c), the matrix A with full row rank;
--   - **(b)** initial primal and dual feasible solutions $\mathbf{x}^0 > \mathbf{0}$, $\mathbf{s}^0 > \mathbf{0}$, $\mathbf{p}^0$;
--   - **(c)** the optimality tolerance $\varepsilon > 0$;
--   - **(d)** the initial barrier parameter $\mu^0$ and the parameter $\alpha$, $0 < \alpha < 1$.
--
--   Steps:
--
--   1. (Initialization) start with $(\mathbf{x}^0, \mathbf{s}^0, \mathbf{p}^0)$, $k = 0$.
--   2. (Optimality test) if $(\mathbf{s}^k)'\mathbf{x}^k < \varepsilon$ stop; else go to Step 3.
--   3. Let $X_k = \mathrm{diag}(x_1^k, \dots, x_n^k)$, $\mu^{k+1} = \alpha\mu^k$.
--   4. (Computation of directions) solve the linear system (9.21)
--
--      $$\mu^{k+1}X_k^{-2}\mathbf{d} - A'\mathbf{p} = \mu^{k+1}X_k^{-1}\mathbf{e} - \mathbf{c}, \qquad A\mathbf{d} = \mathbf{0},$$
--
--      for $\mathbf{p}$ and $\mathbf{d}$ [the Newton step for the barrier problem: $\mathbf{d}$ minimizes the quadratic Taylor approximation of $B_{\mu^{k+1}}(\mathbf{x}^k + \mathbf{d})$ subject to $A\mathbf{d} = \mathbf{0}$].
--   5. (Update of solutions) $\mathbf{x}^{k+1} = \mathbf{x}^k + \mathbf{d}$, $\mathbf{p}^{k+1} = \mathbf{p}$, $\mathbf{s}^{k+1} = \mathbf{c} - A'\mathbf{p}$.
--   6. $k := k + 1$; go to Step 2.
--
--   *Encoding:* Encoded as a predicate on sequences $(\mathbf{x}^k, \mathbf{p}^k, \mathbf{s}^k, \mu^k)$: a step is admissible iff $\mathbf{x}^k > \mathbf{0}$, $\mu^{k+1} = \alpha\mu^k$, and $(\mathbf{d}, \mathbf{p})$ solve (9.21) with the stated updates.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, primal path following algorithm box, pp. 425-426; Newton step derivation pp. 423-424, Eqs. (9.18)-(9.19), (9.21)

import Definitions.Def_LinearOptimization_LogBarrier_CentralPath

/-!
The primal path following algorithm as an iteration predicate.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, §9.4 — the boxed algorithm on pp. 425–426 with the
Newton-direction system (9.21) (derivation pp. 423–424, Eqs. (9.18)–(9.19)).

The algorithm, per iteration `k` (inputs: data `(A, b, c)` with `A` of full
row rank; initial interior primal-dual feasible `(x⁰, s⁰, p⁰)`; tolerance
`ε > 0`; initial barrier parameter `μ⁰` and `0 < α < 1`):

- shrink the barrier parameter: `μ^{k+1} = α μ^k`;
- with `X_k = diag(x^k)`, solve the linear system (9.21) for `(d, p)`:
  `μ^{k+1} X_k^{-2} d − A'p = μ^{k+1} X_k^{-1} e − c` and `Ad = 0`
  (`d` is the Newton step: it minimizes the quadratic Taylor approximation
  of `B_{μ^{k+1}}(x^k + d)` subject to `Ad = 0`);
- update `x^{k+1} = x^k + d`, `p^{k+1} = p`, `s^{k+1} = c − A'p`.

Design (algorithms-are-predicates): `IsPathFollowingRun` constrains the
whole sequence `(x^k, p^k, s^k, μ^k)`; a step is admissible iff `x^k > 0`,
`μ^{k+1} = α μ^k`, and some `d` solves (9.21) with the stated updates.
Since `x^k > 0` is part of admissibility, the diagonal matrices
`X_k^{-1} = diagonal (x^k_j)⁻¹` and `X_k^{-2} = diagonal ((x^k_j)²)⁻¹`
written below are the true inverses (no `Matrix.inv` junk). The
optimality-test stop (step 2 of the box, `(s^k)'x^k < ε`) is NOT baked
into the run predicate: Theorem 9.7 is stated for full runs, whose
`K`-th iterate satisfies the gap bound — running past the test preserves
feasibility and proximity, so this is the book's meaning (recorded in the
mission JSON notes). The closed-form solution (9.19) of the system is
deliberately not baked in either; existence/uniqueness of the Newton
direction stays a lemma, not a definition.
-/

open Matrix

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, Eq. (9.21) (p. 426).** `(d, p)` solve the Newton system of the
barrier problem at the point `x > 0` with barrier parameter `μ`:
`μ X⁻² d − A'p = μ X⁻¹ e − c` and `Ad = 0`, where `X = diag(x)` (the
diagonal inverses are spelled entrywise, exact under the `x > 0` guard of
the run predicate). -/
def IsNewtonBarrierStep {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (mu : ℝ) (x : Fin n → ℝ)
    (d : Fin n → ℝ) (p : Fin m → ℝ) : Prop :=
  mu • (Matrix.diagonal fun j => ((x j) ^ 2)⁻¹).mulVec d - Aᵀ.mulVec p =
      mu • (Matrix.diagonal fun j => (x j)⁻¹).mulVec (fun _ => 1) - c ∧
    A.mulVec d = 0

/-- **Bertsimas & Tsitsiklis, pp. 425–426 (the boxed algorithm as a run predicate).** The
sequences `(x^k, p^k, s^k, μ^k)` form an admissible run of the primal path
following algorithm with barrier-shrinking factor `α`: at every `k`, the
current iterate is interior (`x^k > 0`), `μ^{k+1} = α μ^k`, and some
Newton direction `d` solving (9.21) at `(x^k, μ^{k+1})` produces
`x^{k+1} = x^k + d`, `p^{k+1} = p`, `s^{k+1} = c − A'p^{k+1}`. -/
def IsPathFollowingRun {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (alpha : ℝ) (x : ℕ → Fin n → ℝ)
    (p : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ) (mu : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, (∀ j, 0 < x k j) ∧ mu (k + 1) = alpha * mu k ∧
    ∃ d : Fin n → ℝ,
      IsNewtonBarrierStep A c (mu (k + 1)) (x k) d (p (k + 1)) ∧
      x (k + 1) = x k + d ∧
      s (k + 1) = c - Aᵀ.mulVec (p (k + 1))

end LinearOptimization


