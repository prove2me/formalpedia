-- Prove2me | Theorems.Thm_linear_neumann_off_diagonal_coefficient_entry_as_centered_scalar_fluctuation
-- name    : linear_neumann_off_diagonal_coefficient_entry_as_centered_scalar_fluctuation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-24T14:38:58.739026+00:00
-- url     : https://prove2.me/theorems/1c278311-97af-4a8f-96a2-bca20556c076
-- statement:
--   This theorem identifies one entry of the off-diagonal first Neumann coefficient matrix as a scalar centered-sampling fluctuation.
--
--   Let $p=m/(n_1n_2)$ and fix an output coordinate $w=(a,b)$.  The conditional coefficient matrix from Candes--Recht equation (6.14) has entry
--   $$Q_{\Omega_2}(E)_w
--   =p^{-1}\sum_{w'\ne w}(\delta_{w'}-p)E_{w'}\,\langle P_T(e_{w'}),e_w\rangle.$$
--   With the base matrix
--   $$B^{(w)}_{w'}=\mathbf 1_{w'\ne w}E_{w'}\,\langle P_T(e_{w'}),e_w\rangle,$$
--   the same quantity is exactly
--   $$\sum_{w'}\big[p^{-1}(P_{\Omega_2}-pI)B^{(w)}\big]_{w'}.$$
--
--   This is the algebraic identity that turns each coefficient entry into the scalar Bernstein problem used in Lemma 6.6. Source location: Candes--Recht, Section 6.2, equations (6.13)--(6.14).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_linear_neumann_offdiag_bernstein
open MatrixCompletion

theorem linear_neumann_off_diagonal_coefficient_entry_as_centered_scalar_fluctuation
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega2 : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p : ℝ) (w : Fin n₁ × Fin n₂) :
    linearNeumannOffDiagonalCoefficientMatrix Omega2 S p w.1 w.2 =
      matrixEntrySum
        (centeredSamplingFluctuation Omega2 p
          (linearNeumannOffDiagonalCoefficientBaseMatrix S w)) := by
  sorry
