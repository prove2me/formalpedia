-- Prove2me | solution 1 for ChebotarevDFT.chebPoly_coeff_stair
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:01:17.243369+00:00
-- url     : https://prove2.me/submissions/19ad6e52-982b-46a8-8139-b2b8a9f973fd

-- Sol generated from Novelty/ChebotarevDFT.lean
import Mathlib
import Definitions.Def_Novelty_ChebotarevDFT
import Theorems.Thm_ChebotarevDFT_chebPoly_expansion
import Theorems.Thm_ChebotarevDFT_det_sum_expansion
import Theorems.Thm_ChebotarevDFT_lt_of_sum_eq_stair
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

/-- Each term of the expansion factors as `X ^ (∑ f i)` times a polynomial with known
constant coefficient. -/
theorem term_factor (a : Fin n → ℕ) (f : Fin n → Fin p) (d : ℤ) :
    ∃ U : ℤ[X], (∏ i : Fin n, ((1 + X : ℤ[X]) ^ (a i) - 1) ^ (f i : ℕ)) * C d
        = X ^ (∑ i, (f i : ℕ)) * U ∧ U.coeff 0 = (∏ i, (a i : ℤ) ^ (f i : ℕ)) * d := by
  classical
  choose w hw hw0 using fun i : Fin n => exists_shift (a i)
  refine ⟨(∏ i : Fin n, (w i) ^ (f i : ℕ)) * C d, ?_, ?_⟩
  · simp only [hw, mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, mul_assoc]
  · rw [Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero]
    congr 1
    simp only [← Polynomial.constantCoeff_apply, map_prod, map_pow]
    exact Finset.prod_congr rfl fun i _ => by rw [Polynomial.constantCoeff_apply, hw0]

theorem coeff_term_of_lt (a : Fin n → ℕ) (f : Fin n → Fin p) (d : ℤ)
    (h : stair n < ∑ i, (f i : ℕ)) :
    ((∏ i : Fin n, ((1 + X : ℤ[X]) ^ (a i) - 1) ^ (f i : ℕ)) * C d).coeff (stair n) = 0 := by
  obtain ⟨U, hU, _⟩ := term_factor a f d
  rw [hU, mul_comm, Polynomial.coeff_mul_X_pow']
  simp [Nat.not_le.mpr h]

theorem coeff_term_of_eq (a : Fin n → ℕ) (f : Fin n → Fin p) (d : ℤ)
    (h : ∑ i, (f i : ℕ) = stair n) :
    ((∏ i : Fin n, ((1 + X : ℤ[X]) ^ (a i) - 1) ^ (f i : ℕ)) * C d).coeff (stair n)
      = (∏ i, (a i : ℤ) ^ (f i : ℕ)) * d := by
  obtain ⟨U, hU, hU0⟩ := term_factor a f d
  rw [hU, h, mul_comm, Polynomial.coeff_mul_X_pow']
  simp [hU0]


/-! ## The coefficient is prime to `p` -/




/-! ## The shifted cyclotomic polynomial -/





/-! ## Main theorem -/






open ChebotarevDFT in
theorem solution(a b : Fin n → ℕ) (hb : ∀ j, b j < p) (hnp : n ≤ p) :
    (chebPoly a b).coeff (stair n)
      = (Matrix.vandermonde fun i : Fin n => (a i : ℤ)).det * chooseDet b := by
  classical
  rw [chebPoly_expansion (p := p) a b hb, Polynomial.finset_sum_coeff]
  set F : (Fin n → Fin p) → ℤ := fun f =>
    ((∏ i : Fin n, ((1 + X : ℤ[X]) ^ (a i) - 1) ^ (f i : ℕ)) *
      C ((Matrix.of fun i j : Fin n => ((b j).choose (f i : ℕ) : ℤ)).det)).coeff (stair n) with hF
  set Φ : (Fin n → Fin n) → (Fin n → Fin p) := fun g i => Fin.castLE hnp (g i) with hΦ
  have hΦinj : Function.Injective Φ := by
    intro g₁ g₂ h
    funext i
    have := congrFun h i
    simpa [hΦ] using this
  have hzero : ∀ f ∈ (Finset.univ : Finset (Fin n → Fin p)),
      f ∉ Finset.univ.image Φ → F f = 0 := by
    intro f _ hf
    have hex : ∃ i, n ≤ (f i : ℕ) := by
      by_contra hcon
      push_neg at hcon
      exact hf (Finset.mem_image.mpr ⟨fun i => ⟨f i, hcon i⟩, Finset.mem_univ _,
        by funext i; simp [hΦ]⟩)
    by_cases hinj : Function.Injective f
    · refine coeff_term_of_lt a f _ ?_
      rcases lt_or_eq_of_le (stair_le_sum f hinj) with h | h
      · exact h
      · obtain ⟨i, hi⟩ := hex
        exact absurd (lt_of_sum_eq_stair f hinj h.symm i) (by omega)
    · rw [hF]
      simp [term_eq_zero_of_not_injective b hinj]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image Φ)) hzero]
  rw [Finset.sum_image (fun x _ y _ h => hΦinj h)]
  have hterm : ∀ g : Fin n → Fin n, F (Φ g)
      = (∏ i, (a i : ℤ) ^ (g i : ℕ)) *
        (Matrix.of fun i j : Fin n => ((b j).choose (g i : ℕ) : ℤ)).det := by
    intro g
    by_cases hg : Function.Injective g
    · have hsum : ∑ i, ((Φ g) i : ℕ) = stair n := by
        have hb2 : Function.Bijective g := Finite.injective_iff_bijective.mp hg
        have hs : ∑ i, (g i : ℕ) = ∑ i : Fin n, (i : ℕ) :=
          Fintype.sum_bijective g hb2 _ _ fun i => rfl
        simpa [hΦ, stair, Fin.sum_univ_eq_sum_range (fun i => i) n] using hs
      rw [hF]
      simp only
      rw [coeff_term_of_eq a (Φ g) _ hsum]
      simp [hΦ]
    · have hΦg : ¬ Function.Injective (Φ g) := fun h => hg fun x y hxy => h (by simp [hΦ, hxy])
      rw [hF]
      simp only
      rw [term_eq_zero_of_not_injective b hΦg]
      have hz : (Matrix.of fun i j : Fin n => ((b j).choose (g i : ℕ) : ℤ)).det = 0 := by
        rw [Function.not_injective_iff] at hg
        obtain ⟨i₁, i₂, heq, hne⟩ := hg
        exact Matrix.det_zero_of_row_eq hne (by funext j; simp [heq])
      simp [hz]
  rw [Finset.sum_congr rfl fun g _ => hterm g]
  rw [← det_sum_expansion (fun (i : Fin n) (k : Fin n) => (a i : ℤ) ^ (k : ℕ))
      (fun (k : Fin n) (j : Fin n) => ((b j).choose (k : ℕ) : ℤ))]
  rw [show (Matrix.of fun i j : Fin n =>
        ∑ k : Fin n, (a i : ℤ) ^ (k : ℕ) * ((b j).choose (k : ℕ) : ℤ))
      = (Matrix.vandermonde fun i : Fin n => (a i : ℤ)) *
        (Matrix.of fun k j : Fin n => ((b j).choose (k : ℕ) : ℤ)) from by
    funext i j; simp [Matrix.mul_apply, Matrix.vandermonde_apply]]
  rw [Matrix.det_mul, chooseDet]
  congr 1
  rw [← Matrix.det_transpose]
  rfl
