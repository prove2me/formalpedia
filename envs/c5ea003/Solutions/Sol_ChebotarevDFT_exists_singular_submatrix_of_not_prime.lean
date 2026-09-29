-- Prove2me | solution 1 for ChebotarevDFT.exists_singular_submatrix_of_not_prime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:06:51.390359+00:00
-- url     : https://prove2.me/submissions/01734865-d854-49a4-a016-295970996be1

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





/-! ## Main theorem -/






open ChebotarevDFT in
theorem solution{K : Type*} [Field K] {N : ℕ} {ζ : K}
    (hN : 1 < N) (hnp : ¬ N.Prime) (hζ : IsPrimitiveRoot ζ N) :
    ∃ a b : Fin 2 → ℕ, Function.Injective a ∧ Function.Injective b ∧
      (∀ i, a i < N) ∧ (∀ j, b j < N) ∧
      (Matrix.of fun i j : Fin 2 => ζ ^ (a i * b j)).det = 0 := by
  obtain ⟨d, hdvd, hd2, hdN⟩ := Nat.exists_dvd_of_not_prime2 hN hnp
  obtain ⟨e, he⟩ := hdvd
  have he0 : e ≠ 0 := by rintro rfl; omega
  have he2 : 2 ≤ e := by
    rcases Nat.lt_or_ge e 2 with h | h
    · interval_cases e <;> omega
    · exact h
  have heN : e < N := by nlinarith
  refine ⟨![0, e], ![0, d], ?_, ?_, ?_, ?_, ?_⟩
  · intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
    omega
  · intro i; fin_cases i <;> simp <;> omega
  · intro j; fin_cases j <;> simp <;> omega
  · have hEN : ζ ^ (e * d) = 1 := by
      rw [(mul_comm e d).trans he.symm]
      exact hζ.pow_eq_one
    rw [Matrix.det_fin_two]
    simp [Matrix.of_apply, hEN]
