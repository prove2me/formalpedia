-- Prove2me | Theorems.Thm_summatory_isBigO_rpow_of_dirichlet_partial_bound
-- name    : summatory_isBigO_rpow_of_dirichlet_partial_bound
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T15:20:58.523176+00:00
-- url     : https://prove2.me/theorems/05fa2377-eacb-4dde-aae2-089ecc51281a
-- title:
--   Bounded real-line Dirichlet partial sums force a summatory power bound
-- statement:
--   Let $a:\mathbb N\to\mathbb C$ be any complex sequence and let $\sigma\ge0$. Suppose its ordered Dirichlet partial sums on the real line $\sigma$ are uniformly bounded: there is a real constant $C\ge0$ such that
--
--   $$
--   \left|\sum_{k=1}^{N}\frac{a(k)}{k^\sigma}\right|\le C
--   \qquad\text{for every }N\in\mathbb N.
--   $$
--
--   Then the ordinary summatory function obeys
--
--   $$
--   \sum_{k=1}^{N}a(k)=O(N^\sigma)\qquad(N\to\infty).
--   $$
--
--   The hypothesis requires boundedness of the ordered partial sums; it does not require their convergence or absolute convergence. This provides an arithmetic bridge from a real-axis Dirichlet-polynomial bound to a Mertens-type growth estimate. In the theta Gram-certificate branch of the Masullo RH mission, one can apply it to $a(k)=\mu(k)$ and $\sigma=1/2+\eta$.
--
--   **Formalization Note.** Finite sums use the inclusive interval from $1$ to $N$, so the $N=0$ sum is empty. The natural number $k$ is cast to $\mathbb C$ before taking its complex power with real exponent; the comparison function in the big-O conclusion is the real power of $N$.
-- source:
--   Elementary Abel-summation lemma formalized for the Masullo RH mission. The finite summation identity is Mathlib Finset.sum_range_by_parts, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/BigOperators/Module.lean . Intended application: NymanBeurling.moebius_polynomial_fixed_line_bound, https://prove2.me/theorems/d6f5e94d-d64d-4be3-b952-882091cb75d8 . This is supporting formalization, not a theorem claimed to be extracted from Masullo's paper. The explicit estimate in the proof is 2*C*N^sigma.

import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
open Filter Asymptotics

theorem summatory_isBigO_rpow_of_dirichlet_partial_bound
    (a : ℕ → ℂ) (σ : ℝ) (hσ : 0 ≤ σ)
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖∑ i ∈ Finset.Icc 1 n, a i / (i : ℂ) ^ (σ : ℂ)‖ ≤ C) :
    (fun n : ℕ => ∑ i ∈ Finset.Icc 1 n, a i) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ σ) := by sorry
