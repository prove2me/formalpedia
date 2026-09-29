-- Prove2me | solution 1 for CayleyCensus.walkCount_eq_adj_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-20T13:36:33.211024+00:00
-- url     : https://prove2.me/submissions/0c998148-91af-45c7-a96b-e5d66032fa21

-- Sol generated from MachineLearning/CayleyCensusMoments.lean
import Mathlib
import Definitions.Def_MachineLearning_CayleyCensusInvariance
import Definitions.Def_MachineLearning_CayleyCensusMoments

/-!
# Moments, adjacency powers and return dominance for the Cayley census

This file is the analytic/linear-algebraic half of the census project begun in
`Catalog.MachineLearning.CayleyCensusInvariance`.  Three layers are built on top
of the invariance results proved there.

1. **Concatenation (Chapman–Kolmogorov).**  `walkCount_add` expresses
   `walkCount S (m + n) g` as a convolution of two shorter censuses.  This is
   the semigroup law of the census, and it is what makes the census a *moment
   sequence* rather than a mere counting function.

2. **Return dominance.**  `walkCount_two_mul_le_walkCount_two_mul_one`:
   for an inversion-closed connection set the even-length census is maximised at
   the identity, `walkCount S (2n) g ≤ walkCount S (2n) 1`.  The proof genuinely
   *uses* the inversion symmetry (`walkCount_inv`) — without it the statement is
   false for directed connection sets — combined with the discrete
   Cauchy–Schwarz inequality `2ab ≤ a² + b²` over `ℕ`.
   The identity `walkCount_two_mul_one_eq_sum_sq`,
   `walkCount S (2n) 1 = ∑ h, walkCount S n h ^ 2`, is the second-moment form.

3. **Adjacency bridge.**  `walkCount_eq_adj_pow` identifies the census with
   entries of powers of the Cayley adjacency matrix, `adj_isSymm` shows that
   inversion-closedness is exactly symmetry of that matrix, and `trace_adj_pow`
   gives the trace formula `tr(Aⁿ) = |G| · walkCount S n 1`, the discrete
   analogue of a heat-kernel trace.

## Main results

* `walkCount_add`
* `walkCount_two_mul_one_eq_sum_sq`
* `walkCount_two_mul_le_walkCount_two_mul_one`
* `walkCount_eq_adj_pow`, `adj_isSymm`, `trace_adj_pow`
-/

open CayleyCensus

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]


/-! ### The concatenation (semigroup) law -/




/-! ### The adjacency-matrix bridge -/


omit [Group G] in
/-- Collapsing a `0/1`-weighted sum over the whole group to a sum over `S`. -/
theorem sum_indicator_mul (S : Finset G) (f : G → ℕ) :
    ∑ s : G, (if s ∈ S then 1 else 0) * f s = ∑ s ∈ S, f s := by
  simp [ite_mul, Finset.sum_ite_mem]





open CayleyCensus in
theorem solution(S : Finset G) (n : ℕ) (x y : G) :
    (adj S ^ n) x y = walkCount S n (x⁻¹ * y) := by
  induction n generalizing x y with
  | zero =>
      simp only [pow_zero, Matrix.one_apply, walkCount_zero, inv_mul_eq_one]
  | succ n ih =>
      rw [pow_succ']
      rw [Matrix.mul_apply]
      have hstep : ∀ z : G, adj S x z * (adj S ^ n) z y
          = (if x⁻¹ * z ∈ S then 1 else 0) * walkCount S n (z⁻¹ * y) := by
        intro z; rw [ih]; rfl
      rw [Finset.sum_congr rfl (fun z _ => hstep z)]
      have hre : ∑ z : G, (if x⁻¹ * z ∈ S then 1 else 0) * walkCount S n (z⁻¹ * y)
          = ∑ s : G, (if s ∈ S then 1 else 0) * walkCount S n (s⁻¹ * (x⁻¹ * y)) := by
        refine (Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun s => ?_).symm
        have h1 : x⁻¹ * (x * s) = s := by group
        have h2 : (x * s)⁻¹ * y = s⁻¹ * (x⁻¹ * y) := by group
        simp only [Equiv.coe_mulLeft, h1, h2]
      rw [hre, walkCount_succ]
      exact sum_indicator_mul S (fun s => walkCount S n (s⁻¹ * (x⁻¹ * y)))
