-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.cubic_powerBasis_square_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:43:26.691453+00:00
-- url     : https://prove2.me/submissions/04dddea2-0f05-44b4-9b97-e186b5a0c205

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Mathlib
import Mathlib.RingTheory.PowerBasis

/-!
# Extracting the square-root coordinates from a cubic algebra

The power-basis representation is extracted from the actual square root.
The degree bound then forces all three rational coordinate equations.
No trace, norm, coordinate equation, or coefficient relation is assumed.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11
open Polynomial
open scoped BigOperators

noncomputable section







/-- Every element of an actual three-dimensional power-basis algebra has
three rational coordinates; the coefficients come from its representative. -/
theorem cubic_powerBasis_representation
    {K : Type*} [CommRing K] [Nontrivial K] [Algebra ℚ K]
    (pb : PowerBasis ℚ K) (hdim : pb.dim = 3) (β : K) :
    ∃ x y z : ℚ,
      β = algebraMap ℚ K x * pb.gen^2 + algebraMap ℚ K y * pb.gen +
        algebraMap ℚ K z := by
  obtain ⟨p, hp, hβ⟩ := pb.exists_eq_aeval β
  have hp3 : p.natDegree < 3 := by omega
  refine ⟨p.coeff 2, p.coeff 1, p.coeff 0, ?_⟩
  rw [hβ, Polynomial.aeval_eq_sum_range' hp3]
  simp [Finset.sum_range_succ, Algebra.smul_def]
  ring
end
end ErdosProblems.Erdos243.PaperCompleteR11

open Polynomial
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    {K : Type*} [CommRing K] [Nontrivial K] [Algebra ℚ K]
    (pb : PowerBasis ℚ K) (hdim : pb.dim = 3) (η : ℚ)
    (hroot : pb.gen^3 = pb.gen - algebraMap ℚ K η)
    (β : K) (hsquare : β^2 = pb.gen^2 - 1) :
    ∃ x y z : ℚ,
      β = algebraMap ℚ K x * pb.gen^2 + algebraMap ℚ K y * pb.gen +
        algebraMap ℚ K z ∧
      x^2 + 2*x*z + y^2 - 1 = 0 ∧
      2*x*y + 2*y*z - η*x^2 = 0 ∧
      z^2 - 2*η*x*y + 1 = 0 := by
  obtain ⟨x, y, z, hβ⟩ := cubic_powerBasis_representation pb hdim β
  let q : ℚ[X] := C (x^2 + 2*x*z + y^2 - 1 : ℚ) * X^2 +
    C (2*x*y + 2*y*z - η*x^2 : ℚ) * X + C (z^2 - 2*η*x*y + 1 : ℚ)
  have hqeval : aeval pb.gen q = 0 := by
    simp only [q, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat,
      Polynomial.aeval_C, Polynomial.aeval_X]
    rw [hβ] at hsquare
    linear_combination hsquare -
      ((algebraMap ℚ K x)^2 * pb.gen +
        2 * algebraMap ℚ K x * algebraMap ℚ K y) * hroot
  have hqdeg : q.natDegree ≤ 2 := by
    dsimp [q]
    compute_degree
  have hq : q = 0 := by
    by_contra hq
    have h := pb.dim_le_natDegree_of_root hq hqeval
    omega
  have h1 := congrArg (fun f : ℚ[X] => f.coeff 2) hq
  have h2 := congrArg (fun f : ℚ[X] => f.coeff 1) hq
  have h3 := congrArg (fun f : ℚ[X] => f.coeff 0) hq
  have h1' : x^2 + 2*x*z + y^2 - 1 = 0 := by
    simpa only [q, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero, ite_true, ite_false, show (2 : ℕ) ≠ 1 by decide, show (2 : ℕ) ≠ 0 by decide, add_zero] using h1
  have h2' : 2*x*y + 2*y*z - η*x^2 = 0 := by
    simpa only [q, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero, ite_true, ite_false, show (1 : ℕ) ≠ 2 by decide, show (1 : ℕ) ≠ 0 by decide, zero_add, add_zero] using h2
  have h3' : z^2 - 2*η*x*y + 1 = 0 := by
    simpa only [q, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero, ite_true, ite_false, show (0 : ℕ) ≠ 2 by decide, show (0 : ℕ) ≠ 1 by decide, zero_add] using h3
  exact ⟨x, y, z, hβ, h1', h2', h3'⟩
