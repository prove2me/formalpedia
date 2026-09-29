-- Prove2me | solution 1 for TraceOrder.exists_companion_order_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:29:01.12485+00:00
-- url     : https://prove2.me/submissions/acce7f9f-0743-40a9-b321-aef83a7d7232

-- Sol generated from Applications/CyclicCubicTypeChannel/TraceOrder.lean
import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting
import Definitions.Def_Applications_CyclicCubicTypeChannel_TraceOrder
import Theorems.Thm_CyclicCubic_companion_sq
import Theorems.Thm_CyclicCubic_pow_step
import Theorems.Thm_TraceOrder_companion_pow_of_matrix_pow
import Theorems.Thm_TraceOrder_dvd_sq_sub_one_of_order
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

private lemma card_GL_two_eq :
    Fintype.card (GL (Fin 2) (ZMod p)) = (p ^ 2 - 1) * (p ^ 2 - p) := by
  rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field]
  simp [Fin.prod_univ_two, ZMod.card]




/-- Any non-scalar determinant-one matrix killed by `X^(n+1) - 1` produces a
companion matrix with the same property. -/
theorem exists_comp_of_nonscalar {K : Type*} [Field K] {M : Matrix (Fin 2) (Fin 2) K} {n : ℕ}
    (hdet : M.det = 1) (hpow : M ^ (n + 1) = 1)
    (hns : ∀ c : K, M ≠ c • (1 : Matrix (Fin 2) (Fin 2) K)) :
    ∃ t : K, comp K t ^ (n + 1) = 1 ∧ comp K t ≠ 1 := by
  obtain ⟨h0, h1⟩ := companion_pow_of_matrix_pow hdet hpow hns
  exact ⟨M.trace, comp_pow_eq_one h0 h1, comp_ne_one _⟩





/-! ## Explicit Chebyshev coefficients -/


variable {R : Type*} [CommRing R]








/-! ## Reading the criterion as a congruence -/





variable (p : ℕ) [hp : Fact p.Prime]


/-! ## Conductor 5: the golden-ratio criterion -/


/-! ## Conductor 7: an independent proof of the cyclic-cubic splitting law -/


/-! ## Conductor 11: the quintic criterion -/




open TraceOrder in
set_option maxRecDepth 4000 in
theorem solution{m : ℕ} (hm : m.Prime) (hm2 : m ≠ 2) (hmp : m ≠ p) :
    (∃ t : ZMod p, comp (ZMod p) t ^ m = 1 ∧ comp (ZMod p) t ≠ 1) ↔ m ∣ p ^ 2 - 1 := by
  haveI : Fact m.Prime := ⟨hm⟩
  have hp2 : 2 ≤ p := hp.out.two_le
  constructor
  · rintro ⟨t, hpow, hne⟩
    exact dvd_sq_sub_one_of_order p hm hmp hpow hne
  · intro hdvd
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := hm.two_le; omega⟩
    by_cases hcase : (n + 1) ∣ p - 1
    · -- a primitive `m`-th root of unity already lives in `𝔽_p`
      have hcard : (n + 1) ∣ Fintype.card (ZMod p)ˣ := by
        rwa [ZMod.card_units_eq_totient, Nat.totient_prime hp.out]
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := (ZMod p)ˣ) (n + 1) hcard
      have huone : u ^ (n + 1) = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
      have hvw : (u : ZMod p) * ((u⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 := u.mul_inv
      have hv7 : (u : ZMod p) ^ (n + 1) = 1 := by
        rw [← Units.val_pow_eq_pow_val, huone, Units.val_one]
      have hw7 : ((u⁻¹ : (ZMod p)ˣ) : ZMod p) ^ (n + 1) = 1 := by
        rw [← Units.val_pow_eq_pow_val, inv_pow, huone, inv_one, Units.val_one]
      have hne2 : (u : ZMod p) ≠ ((u⁻¹ : (ZMod p)ˣ) : ZMod p) := by
        intro heq
        have huu : u = u⁻¹ := Units.ext heq
        have hu2 : u ^ 2 = 1 := by
          rw [sq]
          nth_rewrite 2 [huu]
          simp
        have hdvd2 : (n + 1) ∣ 2 := hu ▸ orderOf_dvd_of_pow_eq_one hu2
        have h2le := Nat.le_of_dvd (by norm_num) hdvd2
        have := hm.two_le
        omega
      refine exists_comp_of_nonscalar
        (M := Matrix.diagonal ![(u : ZMod p), ((u⁻¹ : (ZMod p)ˣ) : ZMod p)]) ?_ ?_ ?_
      · rw [Matrix.det_diagonal, Fin.prod_univ_two]
        exact hvw
      · have hfun :
            (![(u : ZMod p), ((u⁻¹ : (ZMod p)ˣ) : ZMod p)] : Fin 2 → ZMod p) ^ (n + 1) = 1 := by
          funext i
          fin_cases i
          · exact hv7
          · exact hw7
        rw [Matrix.diagonal_pow, hfun]
        simp
      · intro c hc
        refine hne2 ?_
        have h00 : (u : ZMod p) = c := by
          have h := congrArg (fun N : Matrix (Fin 2) (Fin 2) (ZMod p) => N 0 0) hc
          simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq,
            smul_eq_mul, mul_one] at h
          exact h
        have h11 : ((u⁻¹ : (ZMod p)ˣ) : ZMod p) = c := by
          have h := congrArg (fun N : Matrix (Fin 2) (Fin 2) (ZMod p) => N 1 1) hc
          simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq,
            smul_eq_mul, mul_one] at h
          exact h
        rw [h00, h11]
    · -- otherwise use Cauchy's theorem inside `GL₂(𝔽_p)`
      have key : ∀ x : ZMod p, x ≠ 0 → x ^ (n + 1) = 1 → x = 1 := by
        intro x hx0 hx
        have h1 : orderOf x ∣ n + 1 := orderOf_dvd_of_pow_eq_one hx
        have h2 : orderOf x ∣ p - 1 :=
          orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hx0)
        rcases hm.eq_one_or_self_of_dvd _ h1 with h | h
        · exact orderOf_eq_one_iff.mp h
        · exact absurd (h ▸ h2) hcase
      have hcard : (n + 1) ∣ Fintype.card (GL (Fin 2) (ZMod p)) := by
        rw [card_GL_two_eq p]
        exact hdvd.mul_right _
      obtain ⟨U, hU⟩ := exists_prime_orderOf_dvd_card (G := GL (Fin 2) (ZMod p)) (n + 1) hcard
      set M : Matrix (Fin 2) (Fin 2) (ZMod p) := (U : Matrix (Fin 2) (Fin 2) (ZMod p)) with hM
      have hMpow : M ^ (n + 1) = 1 := by
        have h : U ^ (n + 1) = 1 := by rw [← hU]; exact pow_orderOf_eq_one U
        have := congrArg (Units.val) h
        simpa [hM] using this
      have hMunit : IsUnit M := hM ▸ U.isUnit
      have hdet0 : M.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det M |>.mp hMunit).ne_zero
      have hdet : M.det = 1 := by
        refine key _ hdet0 ?_
        rw [← Matrix.det_pow, hMpow, Matrix.det_one]
      have hns : ∀ c : ZMod p, M ≠ c • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
        intro c hc
        have hcpow : c ^ (n + 1) = 1 := by
          have h := hMpow
          rw [hc, smul_pow, one_pow] at h
          have h00 := congrArg (fun N : Matrix (Fin 2) (Fin 2) (ZMod p) => N 0 0) h
          simpa [Matrix.one_apply] using h00
        have hc0 : c ≠ 0 := by
          intro h0
          rw [h0, zero_smul] at hc
          rw [hc, Matrix.det_zero ⟨0⟩] at hdet
          exact zero_ne_one hdet
        have hc1 : c = 1 := key c hc0 hcpow
        have hM1 : M = 1 := by rw [hc, hc1, one_smul]
        have hU1 : U = 1 := Units.ext (by simpa [hM] using hM1)
        rw [hU1, orderOf_one] at hU
        have := hm.two_le
        omega
      exact exists_comp_of_nonscalar hdet hMpow hns
