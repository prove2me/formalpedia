-- Prove2me | solution 1 for ChebotarevDFT.lt_of_sum_eq_stair
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:59:57.897768+00:00
-- url     : https://prove2.me/submissions/7996d8f4-50ed-484c-bd9e-eb7338f1ee36

-- Sol generated from Novelty/ChebotarevDFT.lean
import Mathlib
import Definitions.Def_Novelty_ChebotarevDFT
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





/-! ## Polynomial preliminaries -/




/-! ## The auxiliary polynomial -/

variable {n p : ℕ}






/-! ## The lowest coefficient -/





/-! ## The coefficient is prime to `p` -/




/-! ## The shifted cyclotomic polynomial -/





/-! ## Main theorem -/






open ChebotarevDFT in
theorem solution{n p : ℕ} (f : Fin n → Fin p) (hinj : Function.Injective f)
    (h : ∑ i, (f i : ℕ) = stair n) (i0 : Fin n) : (f i0 : ℕ) < n := by
  by_contra hle
  push_neg at hle
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i0.pos; omega⟩
  have hcard : (Finset.univ.erase i0).card = m := by simp [Finset.card_erase_of_mem]
  have h2 := sum_le_sum_of_injOn (Finset.univ.erase i0) (fun i => (f i : ℕ))
    (by intro x _ y _ h; exact hinj (Fin.ext h))
  rw [hcard] at h2
  simp only at h2
  have hsplit : ∑ i, (f i : ℕ) = (f i0 : ℕ) + ∑ i ∈ Finset.univ.erase i0, (f i : ℕ) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i0)).symm
  have hst : stair (m + 1) = stair m + m := by simp [stair, Finset.sum_range_succ]
  have : stair m ≤ ∑ i ∈ Finset.univ.erase i0, (f i : ℕ) := h2
  omega
