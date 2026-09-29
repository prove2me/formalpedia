-- Prove2me | Theorems.Thm_eigenvalue_le_of_quadratic_form_le
-- name    : eigenvalue_le_of_quadratic_form_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-25T02:33:12.38509+00:00
-- url     : https://prove2.me/theorems/31e8f283-5d0f-4f09-8571-0972882aa61d
-- statement:
--   **Eigenvalue bound from a quadratic-form bound.** If a real matrix $A$ is Hermitian and its quadratic form is uniformly dominated, $v^\top A v \le \text{normV}\cdot v^\top v$ for all $v$, then every eigenvalue of $A$ is at most $\text{normV}$. This is the reusable spectral bridge that lets a Hermitian trace-moment engine requiring $\forall i,\ \lambda_i(A) \le \text{normV}$ be discharged from a Loewner domination $A \preceq \text{normV}\cdot I$. Proof: evaluate the quadratic-form hypothesis at the $i$-th (unit-norm) eigenvector $v$; then $v^\top A v = \lambda_i \|v\|^2 = \lambda_i$ and $v^\top v = 1$, so $\lambda_i \le \text{normV}$.
-- source:
--   Standard spectral theory (Rayleigh quotient / Courant-Fischer). The bridge that discharges the matrix-Khintchine trace-moment engine hypothesis (which requires all eigenvalues ≤ normV) from a Loewner / quadratic-form domination A ⪯ normV·I. Candes-Recht 2009 (arXiv:0805.4471) Sec 6.1 application.

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Matrix.Mul
open Matrix
open scoped BigOperators

theorem eigenvalue_le_of_quadratic_form_le {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) (normV : ℝ) (hquad : ∀ v : Fin d → ℝ, (star v ⬝ᵥ A *ᵥ v) ≤ normV * (star v ⬝ᵥ v)) (i : Fin d) : hA.eigenvalues i ≤ normV := by sorry
