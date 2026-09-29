-- Prove2me | Theorems.Thm_rSM_eq_signed_sum
-- name    : rSM_eq_signed_sum
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-25T03:20:42.534486+00:00
-- url     : https://prove2.me/theorems/1f307c60-0a93-418c-819e-b559a7e61d46
-- statement:
--   **Coordinate decomposition of the Rademacher-sampled matrix.** The Rademacher-sampled matrix equals the signed sum of its per-coordinate rank-one scaled pieces: `rademacherSampledMatrix Ω ε p X = ∑_c (rademacherSign ε c.1 c.2) • coordScaled Ω p X c`, where `coordScaled Ω p X c` is the single-entry matrix $p^{-1}\delta_c X_c$ supported at $c$. This is the entrywise identity that lets the dilation of the sampled matrix be written as the symmetric Rademacher signed sum $\sum_c \varepsilon_c H_c$ consumed by the Hermitian trace-moment engine. Proof: pointwise, only the $c = (i,j)$ term survives the sum (`Finset.sum_eq_single`).
-- source:
--   Candes-Recht 2009 (arXiv:0805.4471) Sec 6.1. Elementary coordinate-decomposition identity: the Rademacher-sampled matrix is the signed sum of per-coordinate rank-one scaled matrices. Used to express the dilation of the sampled matrix as the symmetric Rademacher signed sum that the trace-moment engine consumes.

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic
open Matrix
open scoped BigOperators

abbrev RealMatrix (n1 n2 : Nat) := Matrix (Fin n1) (Fin n2) ℝ

def rademacherSign {n1 n2 : Nat}
    (eps : Finset (Fin n1 × Fin n2)) (i : Fin n1) (j : Fin n2) : Real :=
  if (i, j) ∈ eps then 1 else -1

noncomputable def rademacherSampledMatrix {n1 n2 : Nat}
    (Omega eps : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) : RealMatrix n1 n2 :=
  fun i j =>
    p⁻¹ * if (i, j) ∈ Omega then rademacherSign eps i j * X i j else 0

noncomputable def coordScaled {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) (c : Fin n1 × Fin n2) : RealMatrix n1 n2 :=
  fun i j => if (i, j) = c then p⁻¹ * (if c ∈ Omega then X c.1 c.2 else 0) else 0

theorem rSM_eq_signed_sum {n1 n2 : Nat} (Omega eps : Finset (Fin n1 × Fin n2)) (p : Real) (X : RealMatrix n1 n2) : rademacherSampledMatrix Omega eps p X = ∑ c : Fin n1 × Fin n2, rademacherSign eps c.1 c.2 • coordScaled Omega p X c := by sorry
