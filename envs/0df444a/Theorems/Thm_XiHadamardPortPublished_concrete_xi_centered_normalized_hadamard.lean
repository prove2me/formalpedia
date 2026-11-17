-- Prove2me | Theorems.Thm_XiHadamardPortPublished_concrete_xi_centered_normalized_hadamard
-- name    : XiHadamardPortPublished.concrete_xi_centered_normalized_hadamard
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T10:11:49.549677+00:00
-- url     : https://prove2.me/theorems/fb3c478e-5eea-459c-9644-0bac4b9ad227
-- title:
--   Normalized Hadamard product at the symmetry center of the concrete Riemann xi
-- statement:
--   Let \(\xi\) be the classical entire Riemann xi function, normalized by \(\xi(0)=1/2\), and put \(F(z)=\xi(1/2+z)\). Let \((a_i)_{i\in I}\) enumerate the nonzero zeros of F with their exact analytic multiplicities. Then \(F(0)\ne0\), \(\sum_i|a_i|^{-2}<\infty\), and for every \(z\in\mathbb C\),
--   \[
--   \frac{\xi(1/2+z)}{\xi(1/2)}=\prod_{i\in I}\left(1-\frac z{a_i}\right)e^{z/a_i}.
--   \]
--   There is no undetermined exponential factor in this normalized identity. Nonvanishing at the center, the finite-order growth bound, and convergence are proved for the concrete xi function. The product still runs over all centered zeros with multiplicities; regrouping it into the upper/lower pairs used by the project's Q functions is a separate step. This classical identity does not assert that the zeros lie on the critical line.
-- source:
--   Primary formalization: Matteo Cipollina and contributors, PrimeNumberTheoremAnd, Apache-2.0, commit a4fb6989b07e9c76b511807ae93e33e25b820e9b, https://github.com/AlexKontorovich/PrimeNumberTheoremAnd . Lean 4.33.1 compatibility port, dependency bundling and explicit public wrapper by Desenvolvimento RH, coordinated by Ricardo Marangoni Brandao Bueno. No mathematical novelty claimed. Inventory: https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4

import Mathlib
open scoped BigOperators

theorem XiHadamardPortPublished.concrete_xi_centered_normalized_hadamard :
    let f : ℂ → ℂ := fun s => (s*(s-1)*completedRiemannZeta₀ s+1)/2
    let F : ℂ → ℂ := fun z => f (z+1/2)
    let I : Type := {p : ((z : ℂ) × Fin ((MeromorphicOn.divisor F Set.univ z).toNat)) // p.1 ≠ 0}
    let a : I → ℂ := fun p => p.val.1
    F 0 ≠ 0 ∧ Summable (fun i => ‖a i‖⁻¹ ^ (2 : ℕ)) ∧
    ∀ z : ℂ, F z / F 0 = ∏' i : I, ((1-z/a i)*Complex.exp (z/a i)) := by sorry
