-- Prove2me | Theorems.Thm_Hirsch_rref_basis_certificate_restricted_kernel_one_ray
-- name    : Hirsch.rref_basis_certificate_restricted_kernel_one_ray
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T22:10:42.720311+00:00
-- url     : https://prove2.me/theorems/4a5d83c2-d0fa-4e24-93b2-29bb39eb55e8
-- title:
--   Finite basis-row certificates force a one-ray restricted kernel
-- statement:
--   Let A be a real k-by-n linear system, x a candidate vector, and j a nonzero coordinate of x. Suppose that for each nonzero coordinate i of x we have explicit row-combination coefficients dual_i such that, when tested on every standard coordinate column of A, the resulting linear functional equals coordinate i minus (x_i/x_j) times coordinate j. Then every signed null vector of A whose support is contained in the support of x is a scalar multiple of x. Thus finitely many exact basis-column identities certify the one-dimensional restricted-kernel condition used by positive-circuit enumeration. The theorem does not assert that a particular RREF implementation produced the certificates, nor positivity/minimality of x, nor a Hirsch diameter bound.
-- source:
--   Elementary finite-dimensional linear algebra. The column certificates are the dual row relations naturally emitted by exact Gaussian/RREF elimination. Linearity extends them from standard columns to all vectors, after which a support-contained null vector is reconstructed from its pivot coordinate. This is a new executable-certificate adapter for the existing Polynomial Hirsch workspace, not a claim of historical novelty.

import Mathlib
open scoped BigOperators

namespace Hirsch
theorem rref_basis_certificate_restricted_kernel_one_ray
    (n k : ℕ) (A : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    (x : Fin n → ℝ) (j : Fin n) (dual : Fin n → Fin k → ℝ)
    (hxj : x j ≠ 0)
    (hcol : ∀ i, x i ≠ 0 → ∀ l : Fin n,
      (∑ r, dual i r * (A (fun q => if l = q then (1 : ℝ) else 0)) r) =
        (if l = i then 1 else 0) -
          (x i / x j) * (if l = j then 1 else 0)) :
    ∀ z : Fin n → ℝ, A z = 0 →
      Function.support z ⊆ Function.support x → ∃ t : ℝ, z = t • x := by sorry
end Hirsch
