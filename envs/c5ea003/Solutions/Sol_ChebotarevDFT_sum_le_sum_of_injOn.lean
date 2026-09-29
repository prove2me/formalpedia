-- Prove2me | solution 1 for ChebotarevDFT.sum_le_sum_of_injOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:58:30.758508+00:00
-- url     : https://prove2.me/submissions/71faab7c-704a-4bb3-b9e4-ecd7f1f77912

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
theorem solution{ι : Type*} (s : Finset ι) (f : ι → ℕ) (hf : Set.InjOn f s) :
    ∑ i ∈ Finset.range s.card, i ≤ ∑ i ∈ s, f i := by
  classical
  have hinj : Set.InjOn (fun i => (f i : ℤ)) s := by
    intro x hx y hy h
    simp only at h
    exact hf hx hy (by exact_mod_cast h)
  set T : Finset ℤ := s.image (fun i => (f i : ℤ)) with hT
  have hcard : T.card = s.card := Finset.card_image_of_injOn hinj
  have hsum : ∑ x ∈ T, x = ∑ i ∈ s, (f i : ℤ) :=
    Finset.sum_image (by intro x hx y hy h; exact hinj hx hy h)
  have h := Finset.sum_range_le_sum (s := T) (c := 0) (by
    intro x hx
    simp only [hT, Finset.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    positivity)
  rw [hcard, hsum] at h
  simp only [zero_add] at h
  have : ((∑ i ∈ Finset.range s.card, i : ℕ) : ℤ) ≤ ((∑ i ∈ s, f i : ℕ) : ℤ) := by
    push_cast; exact h
  exact_mod_cast this
