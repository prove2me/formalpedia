-- Prove2me | solution 1 for ChebotarevDFT.stair_pow_dvd_chebPoly
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:01:27.251256+00:00
-- url     : https://prove2.me/submissions/2e830fbe-d089-4de7-9389-49f547b5e378

-- Sol generated from Novelty/ChebotarevDFT.lean
import Mathlib
import Definitions.Def_Novelty_ChebotarevDFT
import Theorems.Thm_ChebotarevDFT_chebPoly_expansion
import Theorems.Thm_ChebotarevDFT_sum_le_sum_of_injOn
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



theorem stair_le_sum {n p : ℕ} (f : Fin n → Fin p) (hinj : Function.Injective f) :
    stair n ≤ ∑ i, (f i : ℕ) := by
  have h := sum_le_sum_of_injOn (Finset.univ : Finset (Fin n)) (fun i => (f i : ℕ))
    (by intro x _ y _ h; exact hinj (Fin.ext h))
  simpa [stair] using h


/-! ## Polynomial preliminaries -/

/-- `(1 + X)^m - 1 = X * w` with `w.coeff 0 = m`. -/
theorem exists_shift (m : ℕ) :
    ∃ w : ℤ[X], (1 + X : ℤ[X]) ^ m - 1 = X * w ∧ w.coeff 0 = (m : ℤ) := by
  induction m with
  | zero => exact ⟨0, by ring, by simp⟩
  | succ m ih =>
      obtain ⟨w, hw, hw0⟩ := ih
      refine ⟨(1 + X) * w + 1, ?_, ?_⟩
      · have h : (1 + X : ℤ[X]) ^ (m + 1) - 1 = (1 + X) * ((1 + X) ^ m - 1) + X := by ring
        rw [h, hw]; ring
      · simp [hw0]



/-! ## The auxiliary polynomial -/

variable {n p : ℕ}




/-- Terms of the expansion indexed by a non-injective `f` vanish. -/
theorem term_eq_zero_of_not_injective (b : Fin n → ℕ) {f : Fin n → Fin p}
    (hf : ¬ Function.Injective f) :
    (Matrix.of fun i j : Fin n => ((b j).choose (f i : ℕ) : ℤ)).det = 0 := by
  rw [Function.not_injective_iff] at hf
  obtain ⟨i₁, i₂, heq, hne⟩ := hf
  exact Matrix.det_zero_of_row_eq hne (by funext j; simp [heq])


/-! ## The lowest coefficient -/





/-! ## The coefficient is prime to `p` -/




/-! ## The shifted cyclotomic polynomial -/





/-! ## Main theorem -/






open ChebotarevDFT in
theorem solution(a b : Fin n → ℕ) (hb : ∀ j, b j < p) :
    (X : ℤ[X]) ^ stair n ∣ chebPoly a b := by
  classical
  rw [chebPoly_expansion (p := p) a b hb]
  refine Finset.dvd_sum fun f _ => ?_
  by_cases hinj : Function.Injective f
  · refine Dvd.dvd.mul_right ?_ _
    choose w hw _ using fun i : Fin n => exists_shift (a i)
    have hprod : (∏ i : Fin n, ((1 + X : ℤ[X]) ^ (a i) - 1) ^ (f i : ℕ))
        = X ^ (∑ i, (f i : ℕ)) * ∏ i : Fin n, (w i) ^ (f i : ℕ) := by
      simp only [hw, mul_pow]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [hprod]
    exact Dvd.dvd.mul_right (pow_dvd_pow _ (stair_le_sum f hinj)) _
  · rw [term_eq_zero_of_not_injective b hinj]
    simp
