-- Prove2me | solution 1 for TraceOrder.golden_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:30:27.281115+00:00
-- url     : https://prove2.me/submissions/a13af720-34ce-4833-a3ab-25353d4bc742

-- Sol generated from Applications/CyclicCubicTypeChannel/TraceOrder.lean
import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting
import Definitions.Def_Applications_CyclicCubicTypeChannel_TraceOrder
import Theorems.Thm_CyclicCubic_companion_sq
import Theorems.Thm_CyclicCubic_pow_step
import Theorems.Thm_TraceOrder_companion_pow_of_matrix_pow
import Theorems.Thm_TraceOrder_exists_companion_order_iff
/-
# The Frobenius trace criterion for an arbitrary conductor

## Context (FACT round-32 #3, cycle 2)

`Applications.CyclicCubicTypeChannel.Splitting` settles conductor `7`: the cubic
`X³ + X² − 2X − 1` has a root mod `p` iff `p ≡ ±1 (mod 7)`.  The proof used one
structural fact — the companion matrix of `Y² − xY + 1` has order `7` exactly
when `x = ζ + ζ⁻¹` — which has nothing to do with `7`.

This file isolates that structure for an arbitrary odd prime conductor `m`,
using the Chebyshev-type coefficient sequence

  `A₀ = 0`, `A₁ = 1`, `A_{n+2}(t) = t·A_{n+1}(t) − A_n(t)`,

which satisfies `M^{n+1} = A_{n+1}(t)·M − A_n(t)·I` for every `2 × 2` matrix of
trace `t` and determinant `1`.  Main results:

* `TraceOrder.pow_eq_cheb` — the closed form for powers;
* `TraceOrder.companion_pow_of_matrix_pow` — *any* order-`m` element of
  `SL₂(𝔽_p)` that is not scalar transfers its order to the companion matrix of
  its trace;
* `TraceOrder.exists_companion_order_iff` — for odd primes `m ≠ p`:
  a companion matrix of order `m` exists over `𝔽_p` **iff** `p ≡ ±1 (mod m)`
  (in the form `m ∣ p² − 1`);
* `TraceOrder.cheb_root_iff` — the polynomial form: the pair
  `(A_m, A_{m−1}) = (0, −1)` is solvable over `𝔽_p` iff `m ∣ p² − 1`;
* `TraceOrder.golden_iff` — conductor `5`: `X² + X − 1` has a root mod `p` iff
  `p ≡ ±1 (mod 5)` (the golden-ratio / Fibonacci criterion);
* `TraceOrder.cubic_seven_iff` — conductor `7`: an independent second proof of
  `CyclicCubic.root_iff`, obtained by specialising the general criterion;
* `TraceOrder.quintic_eleven_iff` — conductor `11`: the quintic
  `X⁵ + X⁴ − 4X³ − 3X² + 3X + 1` (minimal polynomial of `ζ₁₁ + ζ₁₁⁻¹`) has a
  root mod `p` iff `p ≡ ±1 (mod 11)`.
-/

open Matrix

open TraceOrder

/-! ## Chebyshev-type coefficients -/


lemma chebA_succ_succ {R : Type*} [CommRing R] (t : R) (n : ℕ) :
    chebA t (n + 2) = t * chebA t (n + 1) - chebA t n := rfl

variable {R : Type*} [CommRing R]

/-- Powers of a trace-`t`, determinant-one `2 × 2` matrix. -/
theorem pow_eq_cheb {M : Matrix (Fin 2) (Fin 2) R} {t : R} (hM : M ^ 2 = t • M - 1) :
    ∀ n : ℕ, M ^ (n + 1) = chebA t (n + 1) • M - chebA t n • 1 := by
  intro n
  induction n with
  | zero => simp [chebA]
  | succ k ih =>
      have h := CyclicCubic.pow_step hM ih
      rw [h, chebA_succ_succ]
      congr 1
      congr 1
      ring

/-! ## The companion matrix -/


lemma comp_sq (t : R) : (comp R t) ^ 2 = t • comp R t - 1 := CyclicCubic.companion_sq t

lemma comp_det (t : R) : (comp R t).det = 1 := by simp [TraceOrder.comp, Matrix.det_fin_two_of]

lemma comp_ne_one [Nontrivial R] (t : R) : comp R t ≠ 1 := by
  intro h
  have h10 : (comp R t) 1 0 = (1 : Matrix (Fin 2) (Fin 2) R) 1 0 := by rw [h]
  simp [TraceOrder.comp] at h10


/-- If the coefficients satisfy `A_m = 0` and `A_{m−1} = −1`, the companion
matrix has order dividing `m`. -/
lemma comp_pow_eq_one [Nontrivial R] {t : R} {n : ℕ} (h0 : chebA t (n + 1) = 0)
    (h1 : chebA t n = -1) : comp R t ^ (n + 1) = 1 := by
  rw [pow_eq_cheb (comp_sq t) n, h0, h1]
  simp

/-! ## Transfer from an arbitrary matrix to a companion matrix -/


variable {K : Type*} [Field K]



/-! ## The order criterion over `𝔽_p` -/


variable (p : ℕ) [hp : Fact p.Prime]



/-- A companion matrix is never a scalar matrix (its `(1,0)` entry is `1`). -/
lemma comp_ne_smul_one {K : Type*} [Field K] (t c : K) :
    comp K t ≠ c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  intro h
  have h10 := congrArg (fun N : Matrix (Fin 2) (Fin 2) K => N 1 0) h
  simp [TraceOrder.comp] at h10

/-- Over a field, the companion matrix of `t` has order dividing `n+1`
exactly when the Chebyshev coefficients take the values `0` and `-1`. -/
theorem comp_pow_eq_one_iff' {K : Type*} [Field K] (t : K) (n : ℕ) :
    comp K t ^ (n + 1) = 1 ↔ chebA t (n + 1) = 0 ∧ chebA t n = -1 := by
  constructor
  · intro h
    have hkey := companion_pow_of_matrix_pow (comp_det t) h (comp_ne_smul_one t)
    have htr : (comp K t).trace = t := by simp [TraceOrder.comp, Matrix.trace_fin_two_of]
    rwa [htr] at hkey
  · rintro ⟨h0, h1⟩
    exact comp_pow_eq_one h0 h1



/-- Polynomial form of the criterion: the Chebyshev coefficient pair
`(A_m, A_{m-1}) = (0, -1)` is solvable over `𝔽_p` iff `m ∣ p² − 1`. -/
theorem cheb_root_iff {m : ℕ} (hm : m.Prime) (hm2 : m ≠ 2) (hmp : m ≠ p) :
    (∃ t : ZMod p, chebA t m = 0 ∧ chebA t (m - 1) = -1) ↔ m ∣ p ^ 2 - 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := hm.two_le; omega⟩
  rw [← exists_companion_order_iff p hm hm2 hmp]
  simp only [Nat.add_sub_cancel]
  constructor
  · rintro ⟨t, h0, h1⟩
    exact ⟨t, (comp_pow_eq_one_iff' t n).mpr ⟨h0, h1⟩, comp_ne_one t⟩
  · rintro ⟨t, hpow, -⟩
    exact ⟨t, (comp_pow_eq_one_iff' t n).mp hpow⟩



/-! ## Explicit Chebyshev coefficients -/


variable {R : Type*} [CommRing R]

lemma chebA_four (t : R) : chebA t 4 = t ^ 3 - 2 * t := by simp [chebA]; ring

lemma chebA_five (t : R) : chebA t 5 = t ^ 4 - 3 * t ^ 2 + 1 := by simp [chebA]; ring






/-! ## Reading the criterion as a congruence -/

private lemma sq_eq_one_zmod5 : ∀ a : ZMod 5, a ^ 2 = 1 ↔ (a = 1 ∨ a = 4) := by decide




variable (p : ℕ) [hp : Fact p.Prime]

/-- `m ∣ p² − 1` is the congruence `p ≡ ±1 (mod m)`, written multiplicatively. -/
lemma dvd_sq_sub_one_iff_sq_cast {m : ℕ} [NeZero m] :
    m ∣ p ^ 2 - 1 ↔ ((p : ZMod m)) ^ 2 = 1 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h : ((p ^ 2 - 1 : ℕ) : ZMod m) = (p : ZMod m) ^ 2 - 1 := by
    rw [Nat.cast_sub hp1]
    push_cast
    ring
  rw [← ZMod.natCast_eq_zero_iff, h, sub_eq_zero]

/-! ## Conductor 5: the golden-ratio criterion -/


/-! ## Conductor 7: an independent proof of the cyclic-cubic splitting law -/


/-! ## Conductor 11: the quintic criterion -/




open TraceOrder in
theorem solution(hp5 : p ≠ 5) :
    (∃ x : ZMod p, x ^ 2 + x - 1 = 0) ↔ ((p : ZMod 5) = 1 ∨ (p : ZMod 5) = 4) := by
  rw [← sq_eq_one_zmod5, ← dvd_sq_sub_one_iff_sq_cast p,
    ← cheb_root_iff p (by norm_num) (by norm_num) (Ne.symm hp5)]
  simp only [show (5 : ℕ) - 1 = 4 from rfl, chebA_five, chebA_four]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by linear_combination (x ^ 2 - x - 1) * hx, by linear_combination (x - 1) * hx⟩
  · rintro ⟨t, h5, h4⟩
    have hfac : (t - 1) * (t ^ 2 + t - 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.mp hfac with h | h
    · exfalso
      have ht : t = 1 := by linear_combination h
      rw [ht] at h5
      have h10 : (1 : ZMod p) = 0 := by linear_combination -h5
      exact one_ne_zero h10
    · exact ⟨t, h⟩
