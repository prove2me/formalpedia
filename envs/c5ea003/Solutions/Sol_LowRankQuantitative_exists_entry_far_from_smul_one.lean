-- Prove2me | solution 1 for LowRankQuantitative.exists_entry_far_from_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:07:26.077056+00:00
-- url     : https://prove2.me/submissions/298d7d27-7c2e-4439-b662-c1e97ef90c97

-- Sol generated from MachineLearning/TransformerUniversality/LowRankQuantitative.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_LowRankQuantitative

/-!
# A quantitative low-rank obstruction for narrow attention heads

`Catalog/MachineLearning/TransformerUniversality/MultiHeadPlumbing.lean` proves the *exact*
low-rank bottleneck for query/key projections: the learned score matrix of a head of width
`dk` is `WQᵀ * WK`, its rank is at most `dk`, and consequently for `dk < d` it can never be
*equal* to the identity score pattern (`qk_ne_one_of_headDim_lt`).

Conjecture 5 of `FUTURE_DIRECTIONS.md` asked for the quantitative version of that statement:
being merely *unequal* to the identity is no obstruction at all in an approximation theory,
since a matrix can be unequal to the identity and yet within `10^{-9}` of it entrywise.  This
file proves the quantitative form, and in the temperature-aware shape that the conjecture
needs.

Main results:

* `exists_entry_far_from_smul_one` — a purely linear-algebraic statement: if
  `S : Matrix (Fin n) (Fin n) ℝ` has rank `< n`, then for every score scale `β ≥ 0` some entry
  of `S` differs from the corresponding entry of `β • 1` by at least `β / n`.  The proof takes
  a kernel vector `v`, normalizes it in the `ℓ¹` norm, and compares the quadratic form of
  `S - β • 1` at `v` (which equals `-β‖v‖₂²`) with its entrywise bound; the gap between the
  `ℓ¹` and `ℓ²` norms — i.e. Cauchy–Schwarz — is exactly where the factor `1/n` comes from.
* `entrywise_distance_to_identity_eq` — **the constant `1/n` is sharp**: the centering matrix
  `1 - (1/n) J` is singular and uniformly `1/n`-close to the identity, so the entrywise
  distance from the identity to the singular matrices is exactly `1/n`;
* `qk_far_from_scaled_identity` — the architectural corollary: for `dk < d`, **no** query/key
  pair of head width `dk` realizes the scaled identity score pattern to entrywise accuracy
  better than `β / d`.
* `qk_no_eps_identity` — the contrapositive as an impossibility statement: an `ε`-accurate
  identity score pattern with `ε < β / d` forces `d ≤ dk`.
* `headDim_lower_bound_of_approx` — the resulting **head-width lower bound**: to implement the
  exact-selection score pattern at scale `β` within entrywise error `ε`, one needs
  `dk ≥ d` whenever `ε < β / d`.

The point of the `β` in these statements is that the obstruction is *scale invariant*: raising
the score scale (equivalently, lowering the softmax temperature) raises the achievable error
floor by exactly the same factor, so the head-width resource of `MultiHeadPlumbing.lean` and
the temperature resource of `SoftmaxLookup.lean` cannot be traded against each other.
-/

open scoped BigOperators

open LowRankQuantitative


variable {n : ℕ}




variable {n : ℕ}








open Matrix

variable {d dk : ℕ}








open LowRankQuantitative in
theorem solution(hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hrank : S.rank < n) {beta : ℝ} (hbeta : 0 ≤ beta) :
    ∃ i j, beta / n ≤ |S i j - beta * (1 : Matrix (Fin n) (Fin n) ℝ) i j| := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- a matrix of non-full rank is singular
  have hdet : S.det = 0 := by
    by_contra hd
    have hu : IsUnit S := (Matrix.isUnit_iff_isUnit_det S).mpr (isUnit_iff_ne_zero.mpr hd)
    have := Matrix.rank_of_isUnit S hu
    simp at this
    omega
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  -- normalize the kernel vector in the ℓ¹ norm
  set A : ℝ := ∑ i, |v i| with hA
  have hApos : 0 < A := by
    rcases Function.ne_iff.mp hv0 with ⟨i, hi⟩
    have hvi : 0 < |v i| := abs_pos.mpr (by simpa using hi)
    exact lt_of_lt_of_le hvi (Finset.single_le_sum (f := fun i => |v i|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  set w : Fin n → ℝ := fun i => v i / A with hw
  have hwsum : ∑ i, |w i| = 1 := by
    simp only [hw, abs_div, abs_of_pos hApos]
    rw [← Finset.sum_div, ← hA, div_self hApos.ne']
  have hSw : ∀ i, ∑ j, S i j * w j = 0 := by
    intro i
    have h0 : ∑ j, S i j * v j = 0 := by
      have := congrFun hv i
      simpa [Matrix.mulVec, dotProduct] using this
    have hsplit : ∑ j, S i j * w j = (∑ j, S i j * v j) / A := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by simp [hw, mul_div_assoc]
    rw [hsplit, h0, zero_div]
  -- the quadratic form of the deviation matrix
  set D : Fin n → Fin n → ℝ :=
    fun i j => S i j - beta * (1 : Matrix (Fin n) (Fin n) ℝ) i j with hD
  have hquad : ∑ i, ∑ j, w i * D i j * w j = -(beta * ∑ i, (w i) ^ 2) := by
    have e1 : ∑ i, ∑ j, w i * S i j * w j = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      have hrow : ∑ j, w i * S i j * w j = w i * ∑ j, S i j * w j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hrow, hSw i, mul_zero]
    have e2 : ∑ i, ∑ j, w i * (beta * (1 : Matrix (Fin n) (Fin n) ℝ) i j) * w j
        = beta * ∑ i, (w i) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · simp; ring
      · intro j _ hj; simp [(Ne.symm hj)]
      · intro h; exact absurd (Finset.mem_univ i) h
    have hsub : ∑ i, ∑ j, w i * D i j * w j
        = (∑ i, ∑ j, w i * S i j * w j)
          - ∑ i, ∑ j, w i * (beta * (1 : Matrix (Fin n) (Fin n) ℝ) i j) * w j := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp [hD]; ring
    rw [hsub, e1, e2, zero_sub]
  -- pick the largest entry of the deviation matrix
  obtain ⟨p, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun p => |D p.1 p.2|) Finset.univ_nonempty
  refine ⟨p.1, p.2, ?_⟩
  set c : ℝ := |D p.1 p.2| with hc
  have hbound : |∑ i, ∑ j, w i * D i j * w j| ≤ c := by
    calc |∑ i, ∑ j, w i * D i j * w j| ≤ ∑ i, |∑ j, w i * D i j * w j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |w i| * c * |w j| := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul, abs_mul]
          have hij := hmax (i, j) (Finset.mem_univ _)
          have h1 : |w i| * |D i j| ≤ |w i| * c := mul_le_mul_of_nonneg_left hij (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = c := by
          have e : ∀ i : Fin n, ∑ j, |w i| * c * |w j| = (|w i| * c) * ∑ j, |w j| :=
            fun i => (Finset.mul_sum _ _ _).symm
          rw [Finset.sum_congr rfl (fun i _ => e i), ← Finset.sum_mul, ← Finset.sum_mul, hwsum]
          ring
  -- Cauchy-Schwarz turns the ℓ¹ normalization into an ℓ² lower bound
  have hcs : (1 : ℝ) ≤ n * ∑ i, (w i) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := fun i => |w i|)
    simpa [hwsum, sq_abs] using h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl2 : (1 : ℝ) / n ≤ ∑ i, (w i) ^ 2 := by
    rw [div_le_iff₀ hn']
    nlinarith
  have hnonneg : (0 : ℝ) ≤ beta * ∑ i, (w i) ^ 2 :=
    mul_nonneg hbeta (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hfinal : beta * ∑ i, (w i) ^ 2 ≤ c := by
    rw [hquad, abs_neg, abs_of_nonneg hnonneg] at hbound
    exact hbound
  have : beta / n ≤ beta * ∑ i, (w i) ^ 2 := by
    rw [div_le_iff₀ hn']
    have : beta * (1 / n) ≤ beta * ∑ i, (w i) ^ 2 := mul_le_mul_of_nonneg_left hl2 hbeta
    calc beta = beta * (1 / n) * n := by field_simp
      _ ≤ (beta * ∑ i, (w i) ^ 2) * n := by nlinarith
  linarith
