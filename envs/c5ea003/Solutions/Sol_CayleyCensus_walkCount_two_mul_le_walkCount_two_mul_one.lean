-- Prove2me | solution 1 for CayleyCensus.walkCount_two_mul_le_walkCount_two_mul_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-20T13:38:00.343919+00:00
-- url     : https://prove2.me/submissions/bc43c347-2292-4375-9e6c-e60c40f9f4bf

-- Sol generated from MachineLearning/CayleyCensusMoments.lean
import Mathlib
import Definitions.Def_MachineLearning_CayleyCensusInvariance
import Definitions.Def_MachineLearning_CayleyCensusMoments
import Theorems.Thm_CayleyCensus_walkCount_add

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

/-- Discrete Cauchy–Schwarz in one variable, over `ℕ` (where `(a - b)^2 ≥ 0` is
unavailable, so we pass through `ℤ`). -/
theorem two_mul_mul_le_sq_add_sq (a b : ℕ) : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by
  have hz : (0 : ℤ) ≤ ((a : ℤ) - (b : ℤ)) ^ 2 := sq_nonneg _
  have hint : (2 * (a * b) : ℤ) ≤ (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by nlinarith
  exact_mod_cast hint

/-! ### The concatenation (semigroup) law -/


/-- Second-moment form of the return count: for an inversion-closed connection
set, the number of closed walks of length `2n` at the identity is the squared
`ℓ²`-norm of the length-`n` census row. -/
theorem walkCount_two_mul_one_eq_sum_sq {S : Finset G} (hS : InvClosed S) (n : ℕ) :
    walkCount S (2 * n) (1 : G) = ∑ h : G, walkCount S n h ^ 2 := by
  have h2 : 2 * n = n + n := by ring
  rw [h2, walkCount_add]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [mul_one, walkCount_inv hS, sq]


/-! ### The adjacency-matrix bridge -/







open CayleyCensus in
theorem solution{S : Finset G} (hS : InvClosed S)
    (n : ℕ) (g : G) : walkCount S (2 * n) g ≤ walkCount S (2 * n) (1 : G) := by
  set a : G → ℕ := fun h => walkCount S n h with ha
  set b : G → ℕ := fun h => walkCount S n (g⁻¹ * h) with hb
  have hsplit : 2 * n = n + n := by ring
  have hg : walkCount S (2 * n) g = ∑ h : G, a h * b h := by
    rw [hsplit, walkCount_add]
    refine Finset.sum_congr rfl fun h _ => ?_
    have hinv : h⁻¹ * g = (g⁻¹ * h)⁻¹ := by group
    rw [ha, hb, hinv, walkCount_inv hS]
  have h1 : walkCount S (2 * n) (1 : G) = ∑ h : G, a h ^ 2 :=
    walkCount_two_mul_one_eq_sum_sq hS n
  -- the two `ℓ²`-masses agree, because `b` is a translate of `a`
  have hshift : ∑ h : G, b h ^ 2 = ∑ h : G, a h ^ 2 :=
    Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ fun h => by simp [ha, hb]
  have hCS : 2 * ∑ h : G, a h * b h ≤ 2 * ∑ h : G, a h ^ 2 := by
    have hterm : ∀ h : G, 2 * (a h * b h) ≤ a h ^ 2 + b h ^ 2 :=
      fun h => two_mul_mul_le_sq_add_sq (a h) (b h)
    calc 2 * ∑ h : G, a h * b h = ∑ h : G, 2 * (a h * b h) := by
            rw [Finset.mul_sum]
      _ ≤ ∑ h : G, (a h ^ 2 + b h ^ 2) := Finset.sum_le_sum fun h _ => hterm h
      _ = (∑ h : G, a h ^ 2) + ∑ h : G, b h ^ 2 := by rw [Finset.sum_add_distrib]
      _ = 2 * ∑ h : G, a h ^ 2 := by rw [hshift]; ring
  rw [hg, h1]
  omega
