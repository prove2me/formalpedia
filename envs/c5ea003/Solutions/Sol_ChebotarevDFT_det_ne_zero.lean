-- Prove2me | solution 1 for ChebotarevDFT.det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:03:56.488156+00:00
-- url     : https://prove2.me/submissions/a2e0aae5-575e-4414-8bfa-e2cfa00e4ca5

-- Sol generated from Novelty/ChebotarevDFT.lean
import Mathlib
import Definitions.Def_Novelty_ChebotarevDFT
import Theorems.Thm_ChebotarevDFT_chebPoly_coeff_stair
import Theorems.Thm_ChebotarevDFT_not_dvd_vandermonde
import Theorems.Thm_ChebotarevDFT_prime_dvd_coeff_of_shiftedCyclotomic_dvd
import Theorems.Thm_ChebotarevDFT_stair_pow_dvd_chebPoly
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


theorem superFactorial_mul_chooseDet (b : Fin n → ℕ) :
    (∏ j : Fin n, (Nat.factorial (j : ℕ) : ℤ)) * chooseDet b
      = (Matrix.vandermonde fun i : Fin n => (b i : ℤ)).det := by
  rw [Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde (fun i => (b i : ℤ))
      (fun j => descPochhammer ℤ j) (fun j => descPochhammer_natDegree ℤ j)
      (fun j => monic_descPochhammer ℤ j)]
  rw [chooseDet, ← Matrix.det_mul_row (fun j : Fin n => (Nat.factorial (j : ℕ) : ℤ))]
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [descPochhammer_eval_eq_descFactorial ℤ, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

theorem not_dvd_chooseDet (hp : p.Prime) (b : Fin n → ℕ) (hb : Function.Injective b)
    (hb' : ∀ j, b j < p) : ¬ ((p : ℤ) ∣ chooseDet b) := by
  intro h
  refine not_dvd_vandermonde hp b hb hb' ?_
  rw [← superFactorial_mul_chooseDet b]
  exact Dvd.dvd.mul_left h _

/-! ## The shifted cyclotomic polynomial -/





/-! ## Main theorem -/






open ChebotarevDFT in
theorem solution{K : Type*} [Field K] [CharZero K] {ζ : K} (hp : p.Prime)
    (hζ : IsPrimitiveRoot ζ p) (a b : Fin n → ℕ)
    (ha : Function.Injective a) (ha' : ∀ i, a i < p)
    (hb : Function.Injective b) (hb' : ∀ j, b j < p) :
    (Matrix.of fun i j : Fin n => ζ ^ (a i * b j)).det ≠ 0 := by
  intro hdet
  have hnp : n ≤ p := by
    have hinj : Function.Injective (fun i : Fin n => (⟨a i, ha' i⟩ : Fin p)) := by
      intro x y h; exact ha (by simpa using congrArg Fin.val h)
    simpa using Fintype.card_le_of_injective _ hinj
  set P := chebPoly a b with hP
  -- Step 1: `P` vanishes at `ζ - 1`.
  have h1 : (Polynomial.aeval (ζ - 1)) P = 0 := by
    rw [hP, chebPoly, AlgHom.map_det (Polynomial.aeval (ζ - 1) : ℤ[X] →ₐ[ℤ] K), ← hdet]
    congr 1
    ext i j
    simp
  -- Step 2: the shifted cyclotomic polynomial divides `P`.
  have h2 : shiftedCyclotomic p ∣ P := by
    have hint : IsIntegral ℤ ζ := by
      refine ⟨X ^ p - C 1, monic_X_pow_sub_C (1 : ℤ) (by have := hp.pos; omega), ?_⟩
      simp [hζ.pow_eq_one]
    have hroot : (Polynomial.aeval ζ) (P.comp (X - 1)) = 0 := by
      rw [Polynomial.aeval_comp]; simpa using h1
    have hdvd : cyclotomic p ℤ ∣ P.comp (X - 1) := by
      rw [Polynomial.cyclotomic_eq_minpoly hζ hp.pos]
      exact minpoly.isIntegrallyClosed_dvd hint hroot
    obtain ⟨D, hD⟩ := hdvd
    refine ⟨D.comp (X + 1), ?_⟩
    have hcomp := congrArg (fun q : ℤ[X] => q.comp (X + 1)) hD
    simp only [Polynomial.mul_comp] at hcomp
    rw [Polynomial.comp_assoc] at hcomp
    simpa [show ((X : ℤ[X]) - 1).comp (X + 1) = X by simp] using hcomp
  -- Step 3: the coefficients below `N` vanish.
  have h3 : ∀ m < stair n, P.coeff m = 0 := by
    obtain ⟨R, hR⟩ := stair_pow_dvd_chebPoly (p := p) a b hb'
    intro m hm
    rw [hP, hR, mul_comm, Polynomial.coeff_mul_X_pow']
    simp [Nat.not_le.mpr hm]
  -- Step 4: `p` would divide the leading coefficient, which is impossible.
  have h4 := prime_dvd_coeff_of_shiftedCyclotomic_dvd hp P (stair n) h2 h3
  rw [hP, chebPoly_coeff_stair (p := p) a b hb' hnp] at h4
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpz.dvd_mul.mp h4 with h | h
  · exact not_dvd_vandermonde hp a ha ha' h
  · exact not_dvd_chooseDet hp b hb hb' h
