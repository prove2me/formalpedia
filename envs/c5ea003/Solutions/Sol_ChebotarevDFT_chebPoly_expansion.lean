-- Prove2me | solution 1 for ChebotarevDFT.chebPoly_expansion
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:58:29.835897+00:00
-- url     : https://prove2.me/submissions/077cdf7a-c8b6-4b0a-80b0-2300ba53c75c

-- Sol generated from Novelty/ChebotarevDFT.lean
import Mathlib
import Definitions.Def_Novelty_ChebotarevDFT
import Theorems.Thm_ChebotarevDFT_det_sum_expansion
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


/-- Binomial expansion with a uniform index range. -/
theorem one_add_pow_eq {R : Type*} [CommRing R] (s : R) (m p : ℕ) (h : m < p) :
    (1 + s) ^ m = ∑ k : Fin p, s ^ (k : ℕ) * (m.choose k : R) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => s ^ k * (m.choose k : R)) p]
  rw [add_comm, add_pow]
  rw [Finset.sum_subset (s₁ := Finset.range (m + 1)) (s₂ := Finset.range p)
      (by intro x hx; simp only [Finset.mem_range] at *; omega)]
  · exact Finset.sum_congr rfl fun k _ => by simp
  · intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp


/-! ## The auxiliary polynomial -/

variable {n p : ℕ}






/-! ## The lowest coefficient -/





/-! ## The coefficient is prime to `p` -/




/-! ## The shifted cyclotomic polynomial -/





/-! ## Main theorem -/






open ChebotarevDFT in
theorem solution(a b : Fin n → ℕ) (hb : ∀ j, b j < p) :
    chebPoly a b = ∑ f : Fin n → Fin p,
      (∏ i : Fin n, ((1 + X : ℤ[X]) ^ (a i) - 1) ^ (f i : ℕ)) *
        C ((Matrix.of fun i j : Fin n => ((b j).choose (f i : ℕ) : ℤ)).det) := by
  classical
  have hentry : ∀ i j : Fin n, (1 + X : ℤ[X]) ^ (a i * b j)
      = ∑ k : Fin p, ((1 + X : ℤ[X]) ^ (a i) - 1) ^ (k : ℕ) * ((b j).choose (k : ℕ) : ℤ[X]) := by
    intro i j
    have h := one_add_pow_eq (R := ℤ[X]) ((1 + X : ℤ[X]) ^ (a i) - 1) (b j) p (hb j)
    rw [show (1 : ℤ[X]) + ((1 + X) ^ (a i) - 1) = (1 + X) ^ (a i) by ring] at h
    rw [pow_mul]
    exact h
  rw [chebPoly, show (Matrix.of fun i j : Fin n => (1 + X : ℤ[X]) ^ (a i * b j))
      = Matrix.of fun i j : Fin n =>
          ∑ k : Fin p, ((1 + X : ℤ[X]) ^ (a i) - 1) ^ (k : ℕ) * ((b j).choose (k : ℕ) : ℤ[X])
      from by funext i j; exact hentry i j]
  rw [det_sum_expansion]
  refine Finset.sum_congr rfl fun f _ => ?_
  congr 1
  rw [RingHom.map_det (Polynomial.C : ℤ →+* ℤ[X])]
  congr 1
