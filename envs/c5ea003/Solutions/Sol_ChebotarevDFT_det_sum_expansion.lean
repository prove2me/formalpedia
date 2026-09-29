-- Prove2me | solution 1 for ChebotarevDFT.det_sum_expansion
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:56:57.94801+00:00
-- url     : https://prove2.me/submissions/09c80e53-3289-498c-8f67-ad976811ddbe

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
theorem solution{R : Type*} [CommRing R] {n m : ℕ} (c : Fin n → Fin m → R)
    (E : Fin m → Fin n → R) :
    (Matrix.of fun i j : Fin n => ∑ k : Fin m, c i k * E k j).det
      = ∑ g : Fin n → Fin m, (∏ i : Fin n, c i (g i)) *
          (Matrix.of fun i j : Fin n => E (g i) j).det := by
  classical
  have hM : (Matrix.of fun i j : Fin n => ∑ k : Fin m, c i k * E k j)
      = (fun i => ∑ k : Fin m, (fun j : Fin n => c i k * E k j)) := by
    funext i j; simp
  rw [show ((Matrix.of fun i j : Fin n => ∑ k : Fin m, c i k * E k j).det)
      = Matrix.detRowAlternating.toMultilinearMap
          (fun i => ∑ k : Fin m, (fun j : Fin n => c i k * E k j)) from by rw [← hM]; rfl]
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  show (Matrix.of fun i j : Fin n => c i (g i) * E (g i) j).det = _
  rw [Matrix.det_mul_column]
  rfl
