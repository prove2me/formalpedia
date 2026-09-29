-- Prove2me | solution 1 for ChebotarevDFT.prime_dvd_coeff_of_shiftedCyclotomic_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:01:23.351558+00:00
-- url     : https://prove2.me/submissions/d6797f22-ec69-4fcf-b8a8-ecaa57af9204

-- Sol generated from Novelty/ChebotarevDFT.lean
import Mathlib
import Definitions.Def_Novelty_ChebotarevDFT
/-
# Chebotarev's theorem on the roots of unity (Chebotarev–Frenkel)

Every square submatrix of the `p × p` DFT matrix `(ζ^{jk})` (`p` prime, `ζ` a primitive
`p`-th root of unity) is nonsingular.

The proof formalized here is Frenkel's argument:

* Let `A = {a i}`, `B = {b j}` be two `n`-element sets of residues mod `p`, and consider the
  integer polynomial `P(X) = det ((1 + X)^{a i * b j})`.
* Expanding `(1 + X)^{a i b j} = (1 + s_i)^{b_j}` with `s_i = (1+X)^{a i} - 1` and using
  multilinearity of the determinant in the rows, `P` is a sum over functions
  `f : Fin n → Fin p` of `(∏ i, s_i ^ f i) * det (choose (b j) (f i))`.
* The terms with non-injective `f` vanish, and the remaining ones are divisible by
  `X ^ (∑ i, f i)` with `∑ i, f i ≥ N := 0 + 1 + ⋯ + (n-1)`. Hence `X^N ∣ P`, and the
  coefficient of `X^N` is `det (vandermonde a) * det (choose (b i) j)`, which is **prime to `p`**
  (a Vandermonde determinant of distinct residues, divided by a superfactorial).
* If some `ζ^{a i b j}` determinant vanished, the shifted cyclotomic polynomial
  `Φ_p(X + 1)` would divide `P`.  Its coefficients are `p ∣ C(p, k+1)` for `k < p - 1` and
  `1` in degree `p - 1`; combined with `X^N ∣ P` this forces `p ∣ P.coeff N`, a contradiction.
-/

open ChebotarevDFT

open Polynomial Matrix Finset

/-! ## Combinatorial preliminaries -/





/-! ## Polynomial preliminaries -/




/-! ## The auxiliary polynomial -/

variable {n p : ℕ}






/-! ## The lowest coefficient -/





/-! ## The coefficient is prime to `p` -/




/-! ## The shifted cyclotomic polynomial -/


theorem X_mul_shiftedCyclotomic (hp : p.Prime) :
    X * shiftedCyclotomic p = (1 + X : ℤ[X]) ^ p - 1 := by
  haveI := Fact.mk hp
  rw [shiftedCyclotomic, Polynomial.cyclotomic_prime ℤ p, Polynomial.sum_comp]
  simp only [Polynomial.X_pow_comp]
  have h := geom_sum_mul (X + 1 : ℤ[X]) p
  rw [show (X + 1 : ℤ[X]) - 1 = X by ring] at h
  rw [mul_comm, h]
  ring_nf

theorem coeff_shiftedCyclotomic (hp : p.Prime) (k : ℕ) :
    (shiftedCyclotomic p).coeff k = (p.choose (k + 1) : ℤ) := by
  have h := X_mul_shiftedCyclotomic hp
  have h2 : (X * shiftedCyclotomic p).coeff (k + 1) = (shiftedCyclotomic p).coeff k :=
    Polynomial.coeff_X_mul _ _
  rw [h] at h2
  rw [← h2, Polynomial.coeff_sub, Polynomial.coeff_one_add_X_pow]
  simp [Polynomial.coeff_one]


/-! ## Main theorem -/






open ChebotarevDFT in
theorem solution(hp : p.Prime) (P : ℤ[X]) (N : ℕ)
    (hdvd : shiftedCyclotomic p ∣ P) (hlow : ∀ m < N, P.coeff m = 0) :
    (p : ℤ) ∣ P.coeff N := by
  obtain ⟨Q, rfl⟩ := hdvd
  set Φ := shiftedCyclotomic p with hΦ
  have hp2 : 2 ≤ p := hp.two_le
  have hΦ0 : Φ.coeff 0 = (p : ℤ) := by rw [hΦ, coeff_shiftedCyclotomic hp]; simp
  have hQ : ∀ m : ℕ, m + (p - 1) ≤ N → Q.coeff m = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      have hcoeff : (Φ * Q).coeff m = Φ.coeff 0 * Q.coeff m := by
        rw [Polynomial.coeff_mul]
        refine Finset.sum_eq_single (0, m) ?_ ?_
        · rintro ⟨k, l⟩ hkl hne
          rw [Finset.mem_antidiagonal] at hkl
          have hl : l < m := by
            rcases Nat.eq_zero_or_pos k with hk | hk
            · exfalso; apply hne; subst hk; simp at hkl ⊢; omega
            · omega
          rw [ih l hl (by omega)]
          ring
        · intro h; exact absurd (Finset.mem_antidiagonal.mpr (by omega)) h
      have hz : (Φ * Q).coeff m = 0 := hlow m (by omega)
      rw [hcoeff, hΦ0] at hz
      have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      exact (mul_eq_zero.mp hz).resolve_left hpne
  rw [Polynomial.coeff_mul]
  refine Finset.dvd_sum ?_
  rintro ⟨k, l⟩ hkl
  rw [Finset.mem_antidiagonal] at hkl
  by_cases hk : k + 1 < p
  · refine Dvd.dvd.mul_right ?_ _
    rw [hΦ, coeff_shiftedCyclotomic hp]
    exact_mod_cast Int.natCast_dvd_natCast.mpr (hp.dvd_choose_self (by omega) hk)
  · rw [hQ l (by omega)]; simp
