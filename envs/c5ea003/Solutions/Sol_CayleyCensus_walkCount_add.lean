-- Prove2me | solution 1 for CayleyCensus.walkCount_add
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-20T13:36:32.213652+00:00
-- url     : https://prove2.me/submissions/aaa05458-eeea-44ab-9b43-92ea1cae9e76

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







open CayleyCensus in
theorem solution(S : Finset G) (m n : ℕ) (g : G) :
    walkCount S (m + n) g = ∑ h : G, walkCount S m h * walkCount S n (h⁻¹ * g) := by
  induction m generalizing g with
  | zero =>
      simp only [Nat.zero_add, walkCount_zero, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq' Finset.univ (1 : G)]
      simp
  | succ m ih =>
      have hsucc : m + 1 + n = (m + n) + 1 := by omega
      rw [hsucc, walkCount_succ]
      have hstep : ∀ s : G, walkCount S (m + n) (s⁻¹ * g)
          = ∑ h : G, walkCount S m h * walkCount S n (h⁻¹ * (s⁻¹ * g)) :=
        fun s => ih _
      rw [Finset.sum_congr rfl (fun s _ => hstep s)]
      -- expand the right-hand side and exchange the two summations
      have hRHS : ∑ h : G, walkCount S (m + 1) h * walkCount S n (h⁻¹ * g)
          = ∑ s ∈ S, ∑ h : G, walkCount S m (s⁻¹ * h) * walkCount S n (h⁻¹ * g) := by
        simp only [walkCount_succ, Finset.sum_mul]
        rw [Finset.sum_comm]
      rw [hRHS]
      refine Finset.sum_congr rfl fun s _ => ?_
      refine (Fintype.sum_equiv (Equiv.mulLeft s⁻¹) _ _ fun h => ?_).symm
      have h2 : (s⁻¹ * h)⁻¹ * (s⁻¹ * g) = h⁻¹ * g := by group
      simp only [Equiv.coe_mulLeft]
      rw [h2]
