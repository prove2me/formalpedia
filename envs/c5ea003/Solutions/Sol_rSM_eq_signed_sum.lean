-- Prove2me | solution 1 for rSM_eq_signed_sum
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:26:26.804175+00:00
-- url     : https://prove2.me/submissions/f563329d-0cff-42c0-ba14-93d25b5050cc

import Mathlib

set_option autoImplicit false

open Matrix
open scoped BigOperators

/-- Local copies of the platform preamble definitions, kept in their own namespace so that
they never clash with the target's top-level declarations. -/
abbrev SignedCoordinateProof.RealMatrix (n1 n2 : Nat) := Matrix (Fin n1) (Fin n2) ℝ

def SignedCoordinateProof.rademacherSign {n1 n2 : Nat}
    (eps : Finset (Fin n1 × Fin n2)) (i : Fin n1) (j : Fin n2) : Real :=
  if (i, j) ∈ eps then 1 else -1

noncomputable def SignedCoordinateProof.rademacherSampledMatrix {n1 n2 : Nat}
    (Omega eps : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : SignedCoordinateProof.RealMatrix n1 n2) : SignedCoordinateProof.RealMatrix n1 n2 :=
  fun i j =>
    p⁻¹ * if (i, j) ∈ Omega then SignedCoordinateProof.rademacherSign eps i j * X i j else 0

noncomputable def SignedCoordinateProof.coordScaled {n1 n2 : Nat}
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : SignedCoordinateProof.RealMatrix n1 n2) (c : Fin n1 × Fin n2) :
    SignedCoordinateProof.RealMatrix n1 n2 :=
  fun i j => if (i, j) = c then p⁻¹ * (if c ∈ Omega then X c.1 c.2 else 0) else 0

open SignedCoordinateProof in
theorem solution {n1 n2 : Nat} (Omega eps : Finset (Fin n1 × Fin n2))
    (p : Real) (X : RealMatrix n1 n2) :
    rademacherSampledMatrix Omega eps p X =
      ∑ c : Fin n1 × Fin n2, rademacherSign eps c.1 c.2 • coordScaled Omega p X c := by
  ext i j
  simp [rademacherSampledMatrix, coordScaled, Matrix.sum_apply, Matrix.smul_apply,
    mul_ite, mul_assoc, mul_left_comm, mul_comm]
