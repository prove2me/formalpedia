-- Prove2me | solution 1 for ChebotarevDFT.not_dvd_vandermonde
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:01:19.847908+00:00
-- url     : https://prove2.me/submissions/fdce5670-a407-4887-9ad8-de5ca2902dea

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
theorem solution(hp : p.Prime) (a : Fin n → ℕ) (ha : Function.Injective a)
    (ha' : ∀ i, a i < p) :
    ¬ ((p : ℤ) ∣ (Matrix.vandermonde fun i : Fin n => (a i : ℤ)).det) := by
  rw [Matrix.det_vandermonde]
  intro hdvd
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rw [hpz.dvd_finset_prod_iff] at hdvd
  obtain ⟨i, _, hi⟩ := hdvd
  rw [hpz.dvd_finset_prod_iff] at hi
  obtain ⟨j, hj, hij⟩ := hi
  have hne : a j ≠ a i := fun h => (Finset.mem_Ioi.mp hj).ne' (ha h)
  obtain ⟨k, hk⟩ := hij
  have h1 := ha' i
  have h2 := ha' j
  have hnz : (a j : ℤ) - (a i : ℤ) ≠ 0 := by
    simp only [sub_ne_zero]; exact_mod_cast hne
  have hp0 : 0 < (p : ℤ) := by exact_mod_cast hp.pos
  rcases lt_trichotomy k 0 with h | h | h
  · nlinarith [hk]
  · simp [h] at hk; exact hnz hk
  · nlinarith [hk]
