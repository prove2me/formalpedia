-- Prove2me | solution 2 for PowerSumSharpness.powerSums_not_determined_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:53:45.288541+00:00
-- url     : https://prove2.me/submissions/c3c71fe8-27b6-4537-8f4a-f6c6d25baa7f

import Mathlib
import Definitions.Def_Probability_PowerSumSharpness

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Probability/PowerSumSharpness.lean ====
/-
# Sharpness of the finite moment problem on `{0, 1, …, N}`

A "distribution" supported in `{0, 1, …, N}` is here a weight function `w : ℕ → ℝ`
(we only ever look at `w` on `Finset.range (N+1)`), and its *power sums* — the moments —
are `powerSum N w k = ∑ i ≤ N, w i * i ^ k`.

The file proves a complete rigidity/sharpness package.

* **Rigidity (`powerSum_determined`).**  Knowing the power sums for all `k ≤ N`
  determines the weights on `{0, …, N}`.  The proof is a Lagrange-interpolation
  (Vandermonde) argument packaged as `eq_zero_of_moments_zero`, which is stated for an
  arbitrary finite family of pairwise distinct real nodes.
* **Sharpness (`powerSums_not_determined_of_lt`).**  The range `k ≤ N` cannot be
  shortened: for every `K < N` there are two genuine probability distributions on
  `{0, …, N}` whose power sums agree for all `k ≤ K` yet which are different — the even
  and odd halves of the binomial weights `i ↦ C(N,i)/2^{N-1}`.  For `N = 2` this is
  exactly the classical pair `{0,2}` versus `{1,1}` (`multiset_zero_two_ne_one_one`).
* **Structure of the failure (`diff_eq_alternating`).**  The failure is *unique*: any two
  weight systems on `{0, …, N}` whose power sums agree for all `k < N` differ by a scalar
  multiple of the alternating binomial vector `i ↦ (-1)^i C(N,i)`.  Thus the collisions at
  `K = N - 1` form a one-parameter family and there are none at `K = N`.
* **Quantitative gap (`powerSum_gap_at_N`).**  For such a pair the `N`-th power sums differ
  by exactly `c · (-1)^N · N !`, where `c` is the weight discrepancy at the node `0`.
  This rests on the sharp alternating-sum identity `alternating_binom_eval`,
  `∑ i ≤ N, (-1)^i C(N,i) p(i) = (-1)^N N! · [X^N] p` for `deg p ≤ N`, proved by induction
  through a finite-difference (Pascal telescoping) argument.
* **Multiset form (`multiset_determined_by_powerSums`).**  Two multisets of naturals bounded
  by `N` with the same power sums `∑ x^k` for `k ≤ N` are equal.
-/

open Finset Polynomial

namespace PowerSumSharpness

/-! ## 1. A Vandermonde / Lagrange vanishing principle -/

/-- The `d`-weighted value of a polynomial of degree `< s.card` at the nodes `v i` is the
corresponding combination of the `d`-weighted moments. -/
theorem sum_eval_eq_moment_combination {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → ℝ}
    {d : ι → ℝ} {p : ℝ[X]} (hp : p.natDegree < s.card) :
    ∑ i ∈ s, d i * p.eval (v i)
      = ∑ k ∈ Finset.range s.card, p.coeff k * ∑ i ∈ s, d i * v i ^ k := by
  have hrw : ∀ i ∈ s, d i * p.eval (v i)
      = ∑ k ∈ Finset.range s.card, p.coeff k * (d i * v i ^ k) := by
    intro i _
    rw [Polynomial.eval_eq_sum_range' hp, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [Finset.sum_congr rfl hrw, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]

/-- If the `d`-weighted moments of the nodes `v i` vanish up to order `s.card - 1`, then the
`d`-weighted value of *every* polynomial of degree `< s.card` vanishes. -/
theorem sum_eval_eq_zero_of_moments_zero {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → ℝ}
    {d : ι → ℝ} (h : ∀ k < s.card, ∑ i ∈ s, d i * v i ^ k = 0)
    {p : ℝ[X]} (hp : p.natDegree < s.card) :
    ∑ i ∈ s, d i * p.eval (v i) = 0 := by
  rw [sum_eval_eq_moment_combination hp]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [h k (Finset.mem_range.mp hk), mul_zero]

/-- **Vandermonde vanishing.**  A weight system on `s.card` pairwise distinct real nodes
whose moments of orders `0, 1, …, s.card - 1` all vanish is identically zero.  This is the
invertibility of the Vandermonde matrix, obtained here from Lagrange interpolation. -/
theorem eq_zero_of_moments_zero {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → ℝ}
    (hv : Set.InjOn v s) {d : ι → ℝ}
    (h : ∀ k < s.card, ∑ i ∈ s, d i * v i ^ k = 0) : ∀ j ∈ s, d j = 0 := by
  intro j hj
  have hcard : 0 < s.card := Finset.card_pos.mpr ⟨j, hj⟩
  have hdeg : (Lagrange.basis s v j).natDegree < s.card := by
    rw [Lagrange.natDegree_basis hv hj]; omega
  have key := sum_eval_eq_zero_of_moments_zero h hdeg
  rw [Finset.sum_eq_single j] at key
  · rwa [Lagrange.eval_basis_self hv hj, mul_one] at key
  · intro i hi hij
    rw [Lagrange.eval_basis_of_ne (Ne.symm hij) hi, mul_zero]
  · intro hc; exact absurd hj hc

/-! ## 2. Power sums of a weight system on `{0, …, N}` -/

/-- The `k`-th power sum (moment) of a weight system `w` supported in `{0, 1, …, N}`. -/
-- [dropped: platform already declares powerSum]
lemma powerSum_sub (N : ℕ) (w v : ℕ → ℝ) (k : ℕ) :
    powerSum N w k - powerSum N v k = ∑ i ∈ range (N + 1), (w i - v i) * (i : ℝ) ^ k := by
  rw [powerSum, powerSum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma natCast_injOn (N : ℕ) : Set.InjOn (fun i : ℕ => (i : ℝ)) (range (N + 1)) :=
  fun _ _ _ _ hab => Nat.cast_injective hab

/-- **Rigidity of the finite moment problem.**  A weight system on `{0, 1, …, N}` is
determined by its power sums of orders `0, 1, …, N`. -/
theorem powerSum_determined {N : ℕ} {w v : ℕ → ℝ}
    (h : ∀ k ≤ N, powerSum N w k = powerSum N v k) : ∀ i ≤ N, w i = v i := by
  intro i hi
  have hz : ∀ k < (range (N + 1)).card,
      ∑ j ∈ range (N + 1), (w j - v j) * ((fun i : ℕ => (i : ℝ)) j) ^ k = 0 := by
    intro k hk
    rw [card_range] at hk
    have := h k (by omega)
    simpa [← powerSum_sub] using sub_eq_zero.mpr this
  have := eq_zero_of_moments_zero (natCast_injOn N) hz i (mem_range.mpr (by omega))
  linarith

/-! ## 3. The alternating binomial functional -/

/-- Shifting the argument by one strictly decreases the degree of the difference. -/
lemma comp_shift_sub_degree_lt {p : ℝ[X]} (hp : p ≠ 0) :
    (p.comp (X + C 1) - p).degree < p.degree := by
  have hX1 : (X + C (1 : ℝ)).natDegree = 1 := Polynomial.natDegree_X_add_C 1
  have hlc : (X + C (1 : ℝ)).leadingCoeff = 1 := Polynomial.monic_X_add_C 1
  have hlead : (p.comp (X + C 1)).leadingCoeff = p.leadingCoeff := by
    rw [Polynomial.leadingCoeff_comp (by rw [hX1]; norm_num), hlc, one_pow, mul_one]
  have hne : p.comp (X + C 1) ≠ 0 := by
    intro h
    rw [h] at hlead
    simp only [Polynomial.leadingCoeff_zero] at hlead
    exact hp (Polynomial.leadingCoeff_eq_zero.mp hlead.symm)
  have hdeg : (p.comp (X + C 1)).degree = p.degree := by
    rw [Polynomial.degree_eq_natDegree hne, Polynomial.degree_eq_natDegree hp,
      Polynomial.natDegree_comp, hX1, mul_one]
  have := Polynomial.degree_sub_lt hdeg hne hlead
  rwa [hdeg] at this

/-- The top coefficient of the finite difference `p(X+1) - p(X)`. -/
lemma coeff_comp_shift_sub (p : ℝ[X]) (N : ℕ) (hp : p.natDegree ≤ N + 1) :
    (p.comp (X + C 1) - p).coeff N = (N + 1) * p.coeff (N + 1) := by
  have h1 : p.comp (X + C (1 : ℝ)) = taylor 1 p := (Polynomial.taylor_apply 1 p).symm
  have hdeg : (Polynomial.hasseDeriv N p).natDegree < 2 := by
    have := Polynomial.natDegree_hasseDeriv_le p N
    omega
  have h2 : (taylor (1 : ℝ) p).coeff N = (Polynomial.hasseDeriv N p).eval 1 :=
    Polynomial.taylor_coeff _ _ _
  rw [Polynomial.eval_eq_sum_range' hdeg] at h2
  simp [Finset.sum_range_succ, Polynomial.hasseDeriv_coeff, Nat.choose_self,
    Nat.choose_succ_self_right, Nat.add_comm] at h2
  rw [Polynomial.coeff_sub, h1, h2]
  ring

/-- **Pascal telescoping.**  The alternating binomial functional of order `N+1` is the
alternating binomial functional of order `N` applied to the finite difference. -/
lemma alternating_binom_succ (N : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ range (N + 2), (-1 : ℝ) ^ i * ((N + 1).choose i) * f i
      = ∑ i ∈ range (N + 1), (-1 : ℝ) ^ i * (N.choose i) * (f i - f (i + 1)) := by
  have hL : ∑ i ∈ range (N + 2), (-1 : ℝ) ^ i * ((N + 1).choose i) * f i
      = (∑ i ∈ range (N + 1), (-1 : ℝ) ^ (i + 1) * ((N + 1).choose (i + 1)) * f (i + 1))
        + ((-1 : ℝ) ^ 0 * ((N + 1).choose 0) * f 0) := Finset.sum_range_succ' _ _
  have hA : ∑ i ∈ range (N + 1), (-1 : ℝ) ^ i * (N.choose i) * f i
      = (∑ i ∈ range N, (-1 : ℝ) ^ (i + 1) * (N.choose (i + 1)) * f (i + 1))
        + ((-1 : ℝ) ^ 0 * (N.choose 0) * f 0) := Finset.sum_range_succ' _ _
  have hsplit : ∑ i ∈ range (N + 1), (-1 : ℝ) ^ i * (N.choose i) * (f i - f (i + 1))
      = (∑ i ∈ range (N + 1), (-1 : ℝ) ^ i * (N.choose i) * f i)
        - ∑ i ∈ range (N + 1), (-1 : ℝ) ^ i * (N.choose i) * f (i + 1) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  have hstep : ∀ i ∈ range (N + 1), (-1 : ℝ) ^ (i + 1) * ((N + 1).choose (i + 1)) * f (i + 1)
      = (-1 : ℝ) ^ (i + 1) * (N.choose (i + 1)) * f (i + 1)
        - (-1 : ℝ) ^ i * (N.choose i) * f (i + 1) := by
    intro i _
    rw [Nat.choose_succ_succ]
    push_cast
    ring
  rw [hL, hsplit, hA, Finset.sum_congr rfl hstep, Finset.sum_sub_distrib,
    Finset.sum_range_succ (f := fun i => (-1 : ℝ) ^ (i + 1) * (N.choose (i + 1)) * f (i + 1))]
  simp [Nat.choose_succ_self]
  ring

/-- **The sharp alternating-sum identity.**  For every polynomial of degree at most `N`,
`∑_{i=0}^{N} (-1)^i C(N,i) p(i) = (-1)^N N! · [X^N]p`.  In particular the functional kills
all polynomials of degree `< N` and detects the leading coefficient in degree `N`. -/
theorem alternating_binom_eval : ∀ (N : ℕ) (p : ℝ[X]), p.degree ≤ (N : WithBot ℕ) →
    ∑ i ∈ range (N + 1), (-1 : ℝ) ^ i * (N.choose i) * p.eval (i : ℝ)
      = (-1 : ℝ) ^ N * (N.factorial : ℝ) * p.coeff N := by
  intro N
  induction N with
  | zero =>
      intro p _
      simp [Polynomial.coeff_zero_eq_eval_zero]
  | succ N ih =>
      intro p hp
      have hpnat : p.natDegree ≤ N + 1 := Polynomial.natDegree_le_iff_degree_le.mpr (by
        exact_mod_cast hp)
      set q : ℝ[X] := p.comp (X + C 1) - p with hq
      have hqdeg : q.degree ≤ (N : WithBot ℕ) := by
        rcases eq_or_ne p 0 with rfl | hp0
        · simp [hq]
        · exact Order.le_of_lt_succ (lt_of_lt_of_le (comp_shift_sub_degree_lt hp0) hp)
      have hev : ∀ i : ℕ, p.eval (i : ℝ) - p.eval ((i + 1 : ℕ) : ℝ) = -q.eval (i : ℝ) := by
        intro i
        simp only [hq, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_C]
        push_cast
        ring
      have hcoeff : q.coeff N = (N + 1) * p.coeff (N + 1) := coeff_comp_shift_sub p N hpnat
      calc ∑ i ∈ range (N + 2), (-1 : ℝ) ^ i * ((N + 1).choose i) * p.eval (i : ℝ)
          = ∑ i ∈ range (N + 1), (-1 : ℝ) ^ i * (N.choose i)
              * (p.eval (i : ℝ) - p.eval ((i + 1 : ℕ) : ℝ)) := by
            simpa using alternating_binom_succ N (fun i => p.eval (i : ℝ))
        _ = -∑ i ∈ range (N + 1), (-1 : ℝ) ^ i * (N.choose i) * q.eval (i : ℝ) := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun i _ => by rw [hev i]; ring
        _ = -((-1 : ℝ) ^ N * (N.factorial : ℝ) * q.coeff N) := by rw [ih q hqdeg]
        _ = (-1 : ℝ) ^ (N + 1) * ((N + 1).factorial : ℝ) * p.coeff (N + 1) := by
            rw [hcoeff, Nat.factorial_succ]
            push_cast
            ring

/-- The alternating binomial functional annihilates all powers below `N`. -/
theorem alternating_binom_pow_lt {N k : ℕ} (hk : k < N) :
    ∑ i ∈ range (N + 1), (-1 : ℝ) ^ i * (N.choose i) * (i : ℝ) ^ k = 0 := by
  have hdeg : (X ^ k : ℝ[X]).degree ≤ (N : WithBot ℕ) := by
    rw [Polynomial.degree_X_pow]
    exact_mod_cast Nat.cast_le.mpr hk.le
  have := alternating_binom_eval N (X ^ k) hdeg
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.coeff_X_pow,
    if_neg (by omega : ¬ N = k), mul_zero] at this
  exact this

/-- At the critical order `N` the alternating binomial functional equals `(-1)^N N!`. -/
theorem alternating_binom_pow_self (N : ℕ) :
    ∑ i ∈ range (N + 1), (-1 : ℝ) ^ i * (N.choose i) * (i : ℝ) ^ N
      = (-1 : ℝ) ^ N * (N.factorial : ℝ) := by
  have hdeg : (X ^ N : ℝ[X]).degree ≤ (N : WithBot ℕ) := le_of_eq (Polynomial.degree_X_pow N)
  have := alternating_binom_eval N (X ^ N) hdeg
  simpa using this

/-! ## 4. Structure of the moment collisions at order `N - 1` -/

/-- **Structure theorem for near-collisions.**  If two weight systems on `{0, 1, …, N}` have
the same power sums for all `k < N`, their difference is the alternating binomial vector
`i ↦ (-1)^i C(N,i)` scaled by the discrepancy at the node `0`.  The space of "invisible"
signed measures is therefore exactly one-dimensional. -/
theorem diff_eq_alternating {N : ℕ} {w v : ℕ → ℝ}
    (h : ∀ k < N, powerSum N w k = powerSum N v k) :
    ∀ i ≤ N, w i - v i = (w 0 - v 0) * ((-1 : ℝ) ^ i * (N.choose i)) := by
  set e : ℕ → ℝ := fun j => (w j - v j) - (w 0 - v 0) * ((-1 : ℝ) ^ j * (N.choose j)) with he
  have he0 : e 0 = 0 := by simp [he]
  have hsum : ∀ k < N, ∑ j ∈ range (N + 1), e j * (j : ℝ) ^ k = 0 := by
    intro k hk
    have h1 : ∑ j ∈ range (N + 1), (w j - v j) * (j : ℝ) ^ k = 0 := by
      rw [← powerSum_sub, h k hk, sub_self]
    have h2 : ∑ j ∈ range (N + 1),
        (w 0 - v 0) * ((-1 : ℝ) ^ j * (N.choose j)) * (j : ℝ) ^ k = 0 := by
      have hfac : ∑ j ∈ range (N + 1), (w 0 - v 0) * ((-1 : ℝ) ^ j * (N.choose j)) * (j : ℝ) ^ k
          = (w 0 - v 0) * ∑ j ∈ range (N + 1), (-1 : ℝ) ^ j * (N.choose j) * (j : ℝ) ^ k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hfac, alternating_binom_pow_lt hk, mul_zero]
    have h3 : ∑ j ∈ range (N + 1), e j * (j : ℝ) ^ k
        = (∑ j ∈ range (N + 1), (w j - v j) * (j : ℝ) ^ k)
          - ∑ j ∈ range (N + 1), (w 0 - v 0) * ((-1 : ℝ) ^ j * (N.choose j)) * (j : ℝ) ^ k := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp only [he]; ring
    rw [h3, h1, h2, sub_zero]
  -- the shifted nodes `1, …, N` carry `N` moment conditions, so the tail of `e` vanishes
  have hshift : ∀ k < (range N).card,
      ∑ i ∈ range N, e (i + 1) * ((fun i : ℕ => ((i + 1 : ℕ) : ℝ)) i) ^ k = 0 := by
    intro k hk
    rw [card_range] at hk
    have := hsum k hk
    rw [Finset.sum_range_succ' (fun j => e j * (j : ℝ) ^ k) N, he0, zero_mul, add_zero] at this
    exact this
  have hinj : Set.InjOn (fun i : ℕ => ((i + 1 : ℕ) : ℝ)) (range N) := by
    intro a _ b _ hab
    have : ((a + 1 : ℕ) : ℝ) = ((b + 1 : ℕ) : ℝ) := hab
    have := Nat.cast_injective this
    omega
  have htail := eq_zero_of_moments_zero hinj hshift
  intro i hi
  match i with
  | 0 => simp
  | (m + 1) =>
      have := htail m (mem_range.mpr (by omega))
      simp only [he] at this
      linarith

/-- **Quantitative sharpness.**  Two weight systems on `{0, …, N}` agreeing in all power sums
of order `< N` have `N`-th power sums differing by exactly `(w 0 - v 0) · (-1)^N · N !`. -/
theorem powerSum_gap_at_N {N : ℕ} {w v : ℕ → ℝ}
    (h : ∀ k < N, powerSum N w k = powerSum N v k) :
    powerSum N w N - powerSum N v N = (w 0 - v 0) * ((-1 : ℝ) ^ N * (N.factorial : ℝ)) := by
  rw [powerSum_sub]
  have : ∀ i ∈ range (N + 1), (w i - v i) * (i : ℝ) ^ N
      = (w 0 - v 0) * ((-1 : ℝ) ^ i * (N.choose i) * (i : ℝ) ^ N) := by
    intro i hi
    rw [diff_eq_alternating h i (by simpa using Nat.lt_succ_iff.mp (mem_range.mp hi))]
    ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, alternating_binom_pow_self]

/-- **Total variation of a moment collision.**  If the power sums agree below order `N`, the
`ℓ¹` distance between the two weight systems is exactly `|w 0 - v 0| · 2^N`. -/
theorem total_variation_eq {N : ℕ} {w v : ℕ → ℝ}
    (h : ∀ k < N, powerSum N w k = powerSum N v k) :
    ∑ i ∈ range (N + 1), |w i - v i| = |w 0 - v 0| * 2 ^ N := by
  have hterm : ∀ i ∈ range (N + 1), |w i - v i| = |w 0 - v 0| * (N.choose i : ℝ) := by
    intro i hi
    rw [diff_eq_alternating h i (Nat.lt_succ_iff.mp (mem_range.mp hi)), abs_mul, abs_mul, abs_pow,
      abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rw [show ∑ i ∈ range (N + 1), (N.choose i : ℝ) = ((∑ i ∈ range (N + 1), N.choose i : ℕ) : ℝ)
      from by push_cast; rfl, Nat.sum_range_choose]
  push_cast
  rfl

/-- A second, independent proof of rigidity: agreement up to order `N` forces the
discrepancy at the node `0` to vanish, hence (by the structure theorem) all discrepancies. -/
theorem powerSum_determined_of_gap {N : ℕ} {w v : ℕ → ℝ}
    (h : ∀ k ≤ N, powerSum N w k = powerSum N v k) : ∀ i ≤ N, w i = v i := by
  have hlt : ∀ k < N, powerSum N w k = powerSum N v k := fun k hk => h k hk.le
  have hgap := powerSum_gap_at_N hlt
  rw [h N le_rfl, sub_self] at hgap
  have hfac : ((-1 : ℝ) ^ N * (N.factorial : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast N.factorial_pos
    positivity
  have hc : w 0 - v 0 = 0 := by
    rcases mul_eq_zero.mp hgap.symm with h1 | h1
    · exact h1
    · exact absurd h1 hfac
  intro i hi
  have := diff_eq_alternating hlt i hi
  rw [hc, zero_mul] at this
  linarith

/-! ## 5. The sharpness construction: even and odd binomial halves -/

/-- The even half of the normalised binomial weights on `{0, 1, …, N}`. -/
-- [dropped: platform already declares evenHalf]
-- [dropped: platform already declares oddHalf]
lemma evenHalf_nonneg (N i : ℕ) : 0 ≤ evenHalf N i := by
  unfold evenHalf; split <;> positivity

lemma oddHalf_nonneg (N i : ℕ) : 0 ≤ oddHalf N i := by
  unfold oddHalf; split <;> positivity

lemma halves_sub (N i : ℕ) :
    evenHalf N i - oddHalf N i = (-1 : ℝ) ^ i * (N.choose i) / 2 ^ (N - 1) := by
  unfold evenHalf oddHalf
  by_cases h : Even i
  · rw [if_pos h, if_pos h, Even.neg_one_pow h]
    ring
  · rw [if_neg h, if_neg h, Odd.neg_one_pow (Nat.not_even_iff_odd.mp h)]
    ring

lemma halves_add (N i : ℕ) :
    evenHalf N i + oddHalf N i = (N.choose i : ℝ) / 2 ^ (N - 1) := by
  unfold evenHalf oddHalf
  split <;> ring

/-- The two halves have the same power sums in every order below `N`. -/
theorem halves_powerSum_agree {N k : ℕ} (hk : k < N) :
    powerSum N (evenHalf N) k = powerSum N (oddHalf N) k := by
  have := powerSum_sub N (evenHalf N) (oddHalf N) k
  rw [show ∑ i ∈ range (N + 1), (evenHalf N i - oddHalf N i) * (i : ℝ) ^ k
        = (∑ i ∈ range (N + 1), (-1 : ℝ) ^ i * (N.choose i) * (i : ℝ) ^ k) / 2 ^ (N - 1) from by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [halves_sub]; ring,
    alternating_binom_pow_lt hk, zero_div] at this
  linarith

/-- Each half is a probability distribution on `{0, 1, …, N}` (for `N ≥ 1`). -/
theorem evenHalf_total {N : ℕ} (hN : 1 ≤ N) : powerSum N (evenHalf N) 0 = 1 := by
  have hsum : powerSum N (evenHalf N) 0 + powerSum N (oddHalf N) 0 = 2 := by
    simp only [powerSum, pow_zero, mul_one]
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun i _ => halves_add N i), ← Finset.sum_div]
    rw [show ∑ i ∈ range (N + 1), (N.choose i : ℝ) = ((∑ i ∈ range (N + 1), N.choose i : ℕ) : ℝ)
        from by push_cast; rfl, Nat.sum_range_choose]
    rw [show N = (N - 1) + 1 from by omega]
    push_cast
    rw [pow_succ]
    field_simp
  have hagree : powerSum N (evenHalf N) 0 = powerSum N (oddHalf N) 0 :=
    halves_powerSum_agree (by omega)
  linarith

theorem oddHalf_total {N : ℕ} (hN : 1 ≤ N) : powerSum N (oddHalf N) 0 = 1 := by
  rw [← halves_powerSum_agree (N := N) (k := 0) (by omega)]
  exact evenHalf_total hN

theorem halves_differ_at_zero {N : ℕ} : evenHalf N 0 ≠ oddHalf N 0 := by
  simp [evenHalf, oddHalf]

/-- The two halves are separated exactly at order `N`, by `N !/2^{N-1}` in absolute value. -/
theorem halves_gap_at_N (N : ℕ) :
    powerSum N (evenHalf N) N - powerSum N (oddHalf N) N
      = (-1 : ℝ) ^ N * (N.factorial : ℝ) / 2 ^ (N - 1) := by
  rw [powerSum_gap_at_N (fun k hk => halves_powerSum_agree hk), halves_sub]
  simp
  ring

/-- **Sharpness of the range `k ≤ N` (`powerSums_not_determined_of_lt`).**
For every `K < N` there are two *different* probability distributions supported in
`{0, 1, …, N}` whose power sums agree for all `k ≤ K`; they are separated exactly at
order `N`.  Hence the moment range `k ≤ N` in `powerSum_determined` cannot be shortened. -/
theorem powerSums_not_determined_of_lt {N K : ℕ} (hN : 1 ≤ N) (hK : K < N) :
    ∃ w v : ℕ → ℝ,
      (∀ i, 0 ≤ w i) ∧ (∀ i, 0 ≤ v i) ∧
      powerSum N w 0 = 1 ∧ powerSum N v 0 = 1 ∧
      (∀ k ≤ K, powerSum N w k = powerSum N v k) ∧
      (∃ i ≤ N, w i ≠ v i) ∧
      powerSum N w N ≠ powerSum N v N := by
  refine ⟨evenHalf N, oddHalf N, evenHalf_nonneg N, oddHalf_nonneg N, evenHalf_total hN,
    oddHalf_total hN, fun k hk => halves_powerSum_agree (by omega),
    ⟨0, Nat.zero_le _, halves_differ_at_zero⟩, ?_⟩
  intro hcon
  have hgap := halves_gap_at_N N
  rw [hcon, sub_self] at hgap
  rcases div_eq_zero_iff.mp hgap.symm with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (pow_ne_zero N (by norm_num))
    · exact absurd h2 (by exact_mod_cast N.factorial_ne_zero)
  · exact absurd h1 (by positivity)

/-! ## 6. Multiset ("empirical distribution") formulation -/

lemma multiset_powerSum_eq {N k : ℕ} {s : Multiset ℕ} (hs : ∀ x ∈ s, x ≤ N) :
    (((s.map (fun x => x ^ k)).sum : ℕ) : ℝ)
      = powerSum N (fun i => (Multiset.count i s : ℝ)) k := by
  rw [Finset.sum_multiset_map_count s (fun x => x ^ k)]
  push_cast [nsmul_eq_mul]
  unfold powerSum
  refine Finset.sum_subset (f := fun i : ℕ => (Multiset.count i s : ℝ) * (i : ℝ) ^ k) ?_ ?_
  · intro x hx
    exact mem_range.mpr (Nat.lt_succ_of_le (hs x (Multiset.mem_toFinset.mp hx)))
  · intro x _ hx
    have : Multiset.count x s = 0 := by
      by_contra hc
      exact hx (Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (Nat.pos_of_ne_zero hc)))
    simp [this]

/-- **Rigidity, multiset form.**  Two finite multisets of naturals bounded by `N` with the
same power sums `∑ x^k` for all `k ≤ N` are equal.  (Equivalently: the empirical
distribution of `N`-bounded data is determined by its first `N` moments.) -/
theorem multiset_determined_by_powerSums {N : ℕ} {s t : Multiset ℕ}
    (hs : ∀ x ∈ s, x ≤ N) (ht : ∀ x ∈ t, x ≤ N)
    (h : ∀ k ≤ N, (s.map (fun x => x ^ k)).sum = (t.map (fun x => x ^ k)).sum) : s = t := by
  have hmom : ∀ k ≤ N, powerSum N (fun i => (Multiset.count i s : ℝ)) k
      = powerSum N (fun i => (Multiset.count i t : ℝ)) k := by
    intro k hk
    rw [← multiset_powerSum_eq hs, ← multiset_powerSum_eq ht, h k hk]
  have hcount := powerSum_determined hmom
  refine Multiset.ext.mpr fun a => ?_
  by_cases ha : a ≤ N
  · exact_mod_cast hcount a ha
  · have h1 : Multiset.count a s = 0 := by
      by_contra hc
      exact ha (hs a (Multiset.count_pos.mp (Nat.pos_of_ne_zero hc)))
    have h2 : Multiset.count a t = 0 := by
      by_contra hc
      exact ha (ht a (Multiset.count_pos.mp (Nat.pos_of_ne_zero hc)))
    rw [h1, h2]

/-- The classical minimal witness: the two-point data sets `{0, 2}` and `{1, 1}` are bounded
by `2`, have the same power sums for `k ≤ 1`, and are different — the `N = 2` instance of
`powerSums_not_determined_of_lt`. -/
theorem multiset_zero_two_ne_one_one :
    (∀ x ∈ ({0, 2} : Multiset ℕ), x ≤ 2) ∧ (∀ x ∈ ({1, 1} : Multiset ℕ), x ≤ 2) ∧
    (∀ k ≤ 1, (({0, 2} : Multiset ℕ).map (fun x => x ^ k)).sum
      = (({1, 1} : Multiset ℕ).map (fun x => x ^ k)).sum) ∧
    (({0, 2} : Multiset ℕ).map (fun x => x ^ 2)).sum
      ≠ (({1, 1} : Multiset ℕ).map (fun x => x ^ 2)).sum ∧
    ({0, 2} : Multiset ℕ) ≠ ({1, 1} : Multiset ℕ) := by
  refine ⟨by decide, by decide, ?_, by decide, by decide⟩
  intro k hk
  interval_cases k <;> decide

/-! ## 7. How large must a moment collision be? -/

lemma multiset_card_eq_powerSum_zero {N : ℕ} {s : Multiset ℕ} (hs : ∀ x ∈ s, x ≤ N) :
    ((Multiset.card s : ℕ) : ℝ) = powerSum N (fun i => (Multiset.count i s : ℝ)) 0 := by
  rw [← multiset_powerSum_eq (k := 0) hs]
  simp

/-- **Minimal size of a moment collision.**  If two different multisets bounded by `N` have
the same power sums for all `k < N`, each of them has at least `2^(N-1)` elements.  The
reason is that their difference must be a nonzero integer multiple of the alternating
binomial vector, whose total variation is `2^N`.  The bound is attained: `{0,2}` for `N = 2`
and `{0,2,2,2}` for `N = 3` (see `multiset_N3_witness`), and in general by the even half of
the binomial weights. -/
theorem multiset_collision_card_lower_bound {N : ℕ} (hN : 1 ≤ N) {s t : Multiset ℕ}
    (hs : ∀ x ∈ s, x ≤ N) (ht : ∀ x ∈ t, x ≤ N)
    (h : ∀ k < N, (s.map (fun x => x ^ k)).sum = (t.map (fun x => x ^ k)).sum)
    (hne : s ≠ t) : 2 ^ (N - 1) ≤ Multiset.card s := by
  set w : ℕ → ℝ := fun i => (Multiset.count i s : ℝ) with hw
  set v : ℕ → ℝ := fun i => (Multiset.count i t : ℝ) with hv
  have hmom : ∀ k < N, powerSum N w k = powerSum N v k := by
    intro k hk
    rw [← multiset_powerSum_eq hs, ← multiset_powerSum_eq ht, h k hk]
  have hstruct := diff_eq_alternating hmom
  -- the discrepancy at the node `0` is a nonzero integer
  have hc : w 0 - v 0 ≠ 0 := by
    intro h0
    refine hne (Multiset.ext.mpr fun a => ?_)
    by_cases ha : a ≤ N
    · have ha' := hstruct a ha
      rw [h0, zero_mul] at ha'
      have : (Multiset.count a s : ℝ) = (Multiset.count a t : ℝ) := by
        simpa [hw, hv] using sub_eq_zero.mp ha'
      exact_mod_cast this
    · have h1 : Multiset.count a s = 0 := by
        by_contra hcc
        exact ha (hs a (Multiset.count_pos.mp (Nat.pos_of_ne_zero hcc)))
      have h2 : Multiset.count a t = 0 := by
        by_contra hcc
        exact ha (ht a (Multiset.count_pos.mp (Nat.pos_of_ne_zero hcc)))
      rw [h1, h2]
  have hm : w 0 - v 0 = (((Multiset.count 0 s : ℤ) - (Multiset.count 0 t : ℤ) : ℤ) : ℝ) := by
    simp [hw, hv]
  have hcabs : (1 : ℝ) ≤ |w 0 - v 0| := by
    rw [hm, ← Int.cast_abs]
    have hne' : ((Multiset.count 0 s : ℤ) - (Multiset.count 0 t : ℤ)) ≠ 0 := by
      intro h0
      exact hc (by rw [hm, h0]; simp)
    exact_mod_cast Int.one_le_abs hne'
  -- the total variation of the difference is `|c| · 2^N`
  have habs : ∑ i ∈ range (N + 1), |w i - v i| = |w 0 - v 0| * 2 ^ N := total_variation_eq hmom
  -- and it is dominated by the total mass of the two multisets
  have hdom : ∑ i ∈ range (N + 1), |w i - v i| ≤ ∑ i ∈ range (N + 1), (w i + v i) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : (0 : ℝ) ≤ w i := by positivity
    have h2 : (0 : ℝ) ≤ v i := by positivity
    rcases abs_cases (w i - v i) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith
  have hmass : ∑ i ∈ range (N + 1), (w i + v i)
      = ((Multiset.card s : ℕ) : ℝ) + ((Multiset.card t : ℕ) : ℝ) := by
    rw [multiset_card_eq_powerSum_zero hs, multiset_card_eq_powerSum_zero ht, powerSum, powerSum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp [hw, hv]
  have hcards : Multiset.card s = Multiset.card t := by
    have := h 0 hN
    simpa using this
  have hfinal : (2 : ℝ) ^ N ≤ 2 * ((Multiset.card s : ℕ) : ℝ) := by
    have hpos : (0 : ℝ) < 2 ^ N := by positivity
    have h1 : (2 : ℝ) ^ N ≤ |w 0 - v 0| * 2 ^ N := by nlinarith
    rw [← habs] at h1
    rw [hmass] at hdom
    have hcR : ((Multiset.card t : ℕ) : ℝ) = ((Multiset.card s : ℕ) : ℝ) := by rw [hcards]
    linarith
  have hpow : (2 : ℝ) ^ N = 2 * 2 ^ (N - 1) := by
    nth_rewrite 1 [show N = (N - 1) + 1 from by omega]
    rw [pow_succ]
    ring
  rw [hpow] at hfinal
  have : ((2 : ℝ) ^ (N - 1)) ≤ ((Multiset.card s : ℕ) : ℝ) := by linarith
  exact_mod_cast this

/-- The `N = 3` witness `{0,2,2,2}` versus `{1,1,1,3}`: the even and odd halves of the
binomial weights `C(3, ·)`.  They agree in all power sums up to order `2`, are separated at
order `3`, and have exactly `2^(3-1) = 4` elements, attaining the bound of
`multiset_collision_card_lower_bound`. -/
theorem multiset_N3_witness :
    (∀ x ∈ ({0, 2, 2, 2} : Multiset ℕ), x ≤ 3) ∧ (∀ x ∈ ({1, 1, 1, 3} : Multiset ℕ), x ≤ 3) ∧
    (∀ k ≤ 2, (({0, 2, 2, 2} : Multiset ℕ).map (fun x => x ^ k)).sum
      = (({1, 1, 1, 3} : Multiset ℕ).map (fun x => x ^ k)).sum) ∧
    (({0, 2, 2, 2} : Multiset ℕ).map (fun x => x ^ 3)).sum
      ≠ (({1, 1, 1, 3} : Multiset ℕ).map (fun x => x ^ 3)).sum ∧
    Multiset.card ({0, 2, 2, 2} : Multiset ℕ) = 2 ^ (3 - 1) := by
  refine ⟨by decide, by decide, ?_, by decide, by decide⟩
  intro k hk
  interval_cases k <;> decide

/-! ## 8. Machine-checked exhaustive search (small cases)

These two statements are the `N = 2` rows of the exhaustive search reported in
`ComputationalEvidence.md`, §8: among sorted tuples with entries in `{0,1,2}`, the pairs
with equal first power sums are exactly the ones predicted by `diff_eq_alternating`, i.e.
those whose count vectors differ by a multiple of `(1, -2, 1)`. -/

set_option maxRecDepth 20000 in
/-- All collisions at `K = N - 1 = 1` among sorted pairs from `{0,1,2}`: only `(0,2)` vs
`(1,1)`. -/
theorem exhaustive_search_N2_pairs :
    ∀ p ∈ (range 3 ×ˢ range 3) ×ˢ (range 3 ×ˢ range 3),
      p.1.1 ≤ p.1.2 → p.2.1 ≤ p.2.2 → p.1.1 + p.1.2 = p.2.1 + p.2.2 →
      (p.1 = p.2 ∨ (p.1 = (0, 2) ∧ p.2 = (1, 1)) ∨ (p.1 = (1, 1) ∧ p.2 = (0, 2))) := by
  decide

set_option maxRecDepth 100000 in
/-- All collisions at `K = N - 1 = 1` among sorted triples from `{0,1,2}`: exactly three
pairs, each a translate of the basic one. -/
theorem exhaustive_search_N2_triples :
    ∀ p ∈ (range 3 ×ˢ range 3 ×ˢ range 3) ×ˢ (range 3 ×ˢ range 3 ×ˢ range 3),
      p.1.1 ≤ p.1.2.1 → p.1.2.1 ≤ p.1.2.2 → p.2.1 ≤ p.2.2.1 → p.2.2.1 ≤ p.2.2.2 →
      p.1.1 + p.1.2.1 + p.1.2.2 = p.2.1 + p.2.2.1 + p.2.2.2 →
      (p.1 = p.2 ∨
        (p.1 = (0, 0, 2) ∧ p.2 = (0, 1, 1)) ∨ (p.1 = (0, 1, 1) ∧ p.2 = (0, 0, 2)) ∨
        (p.1 = (0, 1, 2) ∧ p.2 = (1, 1, 1)) ∨ (p.1 = (1, 1, 1) ∧ p.2 = (0, 1, 2)) ∨
        (p.1 = (0, 2, 2) ∧ p.2 = (1, 1, 2)) ∨ (p.1 = (1, 1, 2) ∧ p.2 = (0, 2, 2))) := by
  decide

/-! ## 9. Extremal separation and stability -/

/-- **The extremal separation constant.**  Among *probability* distributions on `{0, …, N}`
whose power sums agree in all orders `< N`, the `N`-th power sums can differ by at most
`N !/2^(N-1)`.  Equality holds for the even/odd binomial halves (`halves_gap_eq_extremal`),
so the constant is sharp. -/
theorem powerSum_gap_le {N : ℕ} (hN : 1 ≤ N) {w v : ℕ → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hw1 : powerSum N w 0 = 1) (hv1 : powerSum N v 0 = 1)
    (h : ∀ k < N, powerSum N w k = powerSum N v k) :
    |powerSum N w N - powerSum N v N| ≤ (N.factorial : ℝ) / 2 ^ (N - 1) := by
  have htv := total_variation_eq h
  have hdom : ∑ i ∈ range (N + 1), |w i - v i| ≤ ∑ i ∈ range (N + 1), (w i + v i) := by
    refine Finset.sum_le_sum fun i _ => ?_
    rcases abs_cases (w i - v i) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
      linarith [hw i, hv i]
  have hmass : ∑ i ∈ range (N + 1), (w i + v i) = 2 := by
    have h1 : ∑ i ∈ range (N + 1), w i = 1 := by simpa [powerSum] using hw1
    have h2 : ∑ i ∈ range (N + 1), v i = 1 := by simpa [powerSum] using hv1
    rw [Finset.sum_add_distrib, h1, h2]
    norm_num
  have hc : |w 0 - v 0| * 2 ^ N ≤ 2 := by rw [← htv]; linarith
  have hpow : (2 : ℝ) ^ N = 2 * 2 ^ (N - 1) := by
    nth_rewrite 1 [show N = (N - 1) + 1 from by omega]
    rw [pow_succ]; ring
  have hc' : |w 0 - v 0| * 2 ^ (N - 1) ≤ 1 := by rw [hpow] at hc; linarith
  have hgap : |powerSum N w N - powerSum N v N| = |w 0 - v 0| * (N.factorial : ℝ) := by
    rw [powerSum_gap_at_N h, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      Nat.abs_cast]
  rw [hgap, le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (N - 1))]
  have hfac : (0 : ℝ) ≤ (N.factorial : ℝ) := by positivity
  nlinarith

/-- The even/odd binomial halves attain the extremal separation `N !/2^(N-1)`. -/
theorem halves_gap_eq_extremal (N : ℕ) :
    |powerSum N (evenHalf N) N - powerSum N (oddHalf N) N| = (N.factorial : ℝ) / 2 ^ (N - 1) := by
  rw [halves_gap_at_N, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    Nat.abs_cast, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (N - 1))]

/-- The Lebesgue constant of the node set `{0, 1, …, N}` at the node `j`: the `ℓ¹` norm of the
coefficient vector of the `j`-th Lagrange basis polynomial. -/
-- [dropped: platform already declares lagrangeWeight]
theorem powerSum_stability {N : ℕ} {w v : ℕ → ℝ} {eps : ℝ}
    (h : ∀ k ≤ N, |powerSum N w k - powerSum N v k| ≤ eps) :
    ∀ j ≤ N, |w j - v j| ≤ lagrangeWeight N j * eps := by
  intro j hj
  have hjmem : j ∈ range (N + 1) := mem_range.mpr (by omega)
  have hcard : (range (N + 1)).card = N + 1 := card_range _
  have hdeg : (Lagrange.basis (range (N + 1)) (fun i : ℕ => (i : ℝ)) j).natDegree
      < (range (N + 1)).card := by
    rw [Lagrange.natDegree_basis (natCast_injOn N) hjmem, hcard]
    omega
  have hkey := sum_eval_eq_moment_combination (v := fun i : ℕ => (i : ℝ))
    (d := fun i => w i - v i) hdeg
  rw [Finset.sum_eq_single j] at hkey
  · rw [Lagrange.eval_basis_self (natCast_injOn N) hjmem, mul_one, hcard] at hkey
    simp only at hkey
    rw [hkey]
    calc |∑ k ∈ range (N + 1),
            (Lagrange.basis (range (N + 1)) (fun i : ℕ => (i : ℝ)) j).coeff k *
              ∑ i ∈ range (N + 1), (w i - v i) * (i : ℝ) ^ k|
        ≤ ∑ k ∈ range (N + 1),
            |(Lagrange.basis (range (N + 1)) (fun i : ℕ => (i : ℝ)) j).coeff k *
              ∑ i ∈ range (N + 1), (w i - v i) * (i : ℝ) ^ k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range (N + 1),
            |(Lagrange.basis (range (N + 1)) (fun i : ℕ => (i : ℝ)) j).coeff k| * eps := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [abs_mul, ← powerSum_sub]
          exact mul_le_mul_of_nonneg_left (h k (Nat.lt_succ_iff.mp (mem_range.mp hk)))
            (abs_nonneg _)
      _ = lagrangeWeight N j * eps := by rw [lagrangeWeight, Finset.sum_mul]
  · intro i hi hij
    rw [Lagrange.eval_basis_of_ne (Ne.symm hij) hi, mul_zero]
  · intro hcon
    exact absurd hjmem hcon

/-! ## 10. The collision-size bound `2^(N-1)` is attained for every `N` -/

/-- The data set carrying the even half of the binomial weights `C(N, ·)`. -/
-- [dropped: platform already declares evenMultiset]
-- [dropped: platform already declares oddMultiset]
lemma count_evenMultiset (N j : ℕ) :
    Multiset.count j (evenMultiset N) = if Even j then N.choose j else 0 := by
  rw [evenMultiset, Multiset.count_sum']
  have hterm : ∀ i ∈ range (N + 1),
      Multiset.count j (if Even i then Multiset.replicate (N.choose i) i else 0)
        = if i = j then (if Even j then N.choose j else 0) else 0 := by
    intro i _
    by_cases hi : Even i
    · rw [if_pos hi, Multiset.count_replicate]
      by_cases hij : i = j
      · subst hij; simp [hi]
      · simp [hij]
    · rw [if_neg hi]
      by_cases hij : i = j
      · subst hij; simp [hi]
      · simp [hij]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (range (N + 1)) j]
  by_cases hj : j ∈ range (N + 1)
  · rw [if_pos hj]
  · rw [if_neg hj, Nat.choose_eq_zero_of_lt (by simpa using hj)]
    simp

lemma count_oddMultiset (N j : ℕ) :
    Multiset.count j (oddMultiset N) = if Even j then 0 else N.choose j := by
  rw [oddMultiset, Multiset.count_sum']
  have hterm : ∀ i ∈ range (N + 1),
      Multiset.count j (if Even i then 0 else Multiset.replicate (N.choose i) i)
        = if i = j then (if Even j then 0 else N.choose j) else 0 := by
    intro i _
    by_cases hi : Even i
    · rw [if_pos hi]
      by_cases hij : i = j
      · subst hij; simp [hi]
      · simp [hij]
    · rw [if_neg hi, Multiset.count_replicate]
      by_cases hij : i = j
      · subst hij; simp [hi]
      · simp [hij]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (range (N + 1)) j]
  by_cases hj : j ∈ range (N + 1)
  · rw [if_pos hj]
  · rw [if_neg hj, Nat.choose_eq_zero_of_lt (by simpa using hj)]
    simp

lemma mem_evenMultiset_le (N : ℕ) : ∀ x ∈ evenMultiset N, x ≤ N := by
  intro x hx
  by_contra hcon
  have : Multiset.count x (evenMultiset N) = 0 := by
    rw [count_evenMultiset, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  exact absurd (Multiset.count_pos.mpr hx) (by omega)

lemma mem_oddMultiset_le (N : ℕ) : ∀ x ∈ oddMultiset N, x ≤ N := by
  intro x hx
  by_contra hcon
  have : Multiset.count x (oddMultiset N) = 0 := by
    rw [count_oddMultiset, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  exact absurd (Multiset.count_pos.mpr hx) (by omega)

lemma powerSum_evenMultiset (N k : ℕ) :
    powerSum N (fun i => (Multiset.count i (evenMultiset N) : ℝ)) k
      = 2 ^ (N - 1) * powerSum N (evenHalf N) k := by
  unfold powerSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [count_evenMultiset]
  unfold evenHalf
  have h2 : (2 : ℝ) ^ (N - 1) ≠ 0 := by positivity
  by_cases hi : Even i
  · rw [if_pos hi, if_pos hi]
    field_simp
  · rw [if_neg hi, if_neg hi]
    simp

lemma powerSum_oddMultiset (N k : ℕ) :
    powerSum N (fun i => (Multiset.count i (oddMultiset N) : ℝ)) k
      = 2 ^ (N - 1) * powerSum N (oddHalf N) k := by
  unfold powerSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [count_oddMultiset]
  unfold oddHalf
  have h2 : (2 : ℝ) ^ (N - 1) ≠ 0 := by positivity
  by_cases hi : Even i
  · rw [if_pos hi, if_pos hi]
    simp
  · rw [if_neg hi, if_neg hi]
    field_simp

lemma card_evenMultiset {N : ℕ} (hN : 1 ≤ N) : Multiset.card (evenMultiset N) = 2 ^ (N - 1) := by
  have hreal : ((Multiset.card (evenMultiset N) : ℕ) : ℝ) = 2 ^ (N - 1) := by
    rw [multiset_card_eq_powerSum_zero (mem_evenMultiset_le N), powerSum_evenMultiset,
      evenHalf_total hN, mul_one]
  exact_mod_cast hreal

/-- **The collision-size bound is sharp for every `N`.**  The even and odd halves of the
binomial data `C(N, ·)` are two different data sets bounded by `N`, of size exactly
`2^(N-1)`, whose power sums agree in every order `k < N`.  Together with
`multiset_collision_card_lower_bound` this pins down the exact threshold `2^(N-1)` at which
moment collisions of order `N - 1` begin to exist. -/
theorem collision_card_bound_sharp {N : ℕ} (hN : 1 ≤ N) :
    (∀ x ∈ evenMultiset N, x ≤ N) ∧ (∀ x ∈ oddMultiset N, x ≤ N) ∧
    (∀ k < N, ((evenMultiset N).map (fun x => x ^ k)).sum
      = ((oddMultiset N).map (fun x => x ^ k)).sum) ∧
    evenMultiset N ≠ oddMultiset N ∧
    Multiset.card (evenMultiset N) = 2 ^ (N - 1) := by
  refine ⟨mem_evenMultiset_le N, mem_oddMultiset_le N, ?_, ?_, card_evenMultiset hN⟩
  · intro k hk
    have hreal : ((((evenMultiset N).map (fun x => x ^ k)).sum : ℕ) : ℝ)
        = ((((oddMultiset N).map (fun x => x ^ k)).sum : ℕ) : ℝ) := by
      rw [multiset_powerSum_eq (mem_evenMultiset_le N), multiset_powerSum_eq (mem_oddMultiset_le N),
        powerSum_evenMultiset, powerSum_oddMultiset, halves_powerSum_agree hk]
    exact_mod_cast hreal
  · intro hcon
    have h0 : Multiset.count 0 (evenMultiset N) = Multiset.count 0 (oddMultiset N) := by
      rw [hcon]
    rw [count_evenMultiset, count_oddMultiset] at h0
    simp at h0

end PowerSumSharpness
section
open Finset Polynomial
open PowerSumSharpness

theorem solution {N K : ℕ} (hN : 1 ≤ N) (hK : K < N) :
    ∃ w v : ℕ → ℝ,
      (∀ i, 0 ≤ w i) ∧ (∀ i, 0 ≤ v i) ∧
      powerSum N w 0 = 1 ∧ powerSum N v 0 = 1 ∧
      (∀ k ≤ K, powerSum N w k = powerSum N v k) ∧
      (∃ i ≤ N, w i ≠ v i) ∧
      powerSum N w N ≠ powerSum N v N := by
  first
  | exact PowerSumSharpness.powerSums_not_determined_of_lt hN hK
  | exact PowerSumSharpness.powerSums_not_determined_of_lt
  | exact @PowerSumSharpness.powerSums_not_determined_of_lt N K hN hK
  | apply PowerSumSharpness.powerSums_not_determined_of_lt
  | exact PowerSumSharpness.powerSums_not_determined_of_lt ..


end
