-- Prove2me | solution 1 for AdjSum.trace_invAdjMatZ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:11:34.542347+00:00
-- url     : https://prove2.me/submissions/9c437695-75f7-4ed9-9745-3892d9d617d0

-- Sol generated from Applications/AdjacentSumPolytopes/Inverse.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Inverse

/-!
# The inverse transfer matrix, its square, and the linear charpoly coefficient

`Determinant.lean` proved that the adjacent-sum transfer matrix `A = adjMat s` is
unimodular.  Here we exhibit its inverse **explicitly**: it is the *anti-bidiagonal*
`0, ±1` matrix

`B a b = [a + b = s] − [a + b = s + 1]`,

so that `A · B = B · A = 1` over `ℤ`.  Two structural consequences follow.

* **The square of the inverse is a path Laplacian.**  `B² = neumannLaplacian s`, the
  tridiagonal matrix with diagonal `1, 2, 2, …, 2` and off-diagonal `−1`, i.e. the
  Laplacian of the path on `s + 1` vertices with one Dirichlet and one Neumann end.  This
  is a *structural explanation* of the cosecant spectrum proved analytically in
  `SecantSpectrum.lean`: the eigenvalues of that Laplacian are `4 sin²((2t+1)π/(2(2s+3)))`,
  and `λ_t = ±1/(2 sin((2t+1)π/(2(2s+3))))` are exactly the numbers whose inverse squares
  they are.

* **A new case of the binomial staircase conjecture.**  Because `A⁻¹` is explicit, the
  *reverse* of the characteristic polynomial is the characteristic polynomial of `B` up to
  the unit `det A`, and therefore the coefficient of `x¹` in `det(x I − A)` is
  `−det(A) · (−1)^{s+1} · tr(B) = (−1)^{⌊(s+1)/2⌋}`.  This is the `m = s` case of
  Conjecture 1 of `FUTURE_DIRECTIONS.md`, whose prediction there is
  `(−1)^{⌊(s+1)/2⌋} · C(s, s) = (−1)^{⌊(s+1)/2⌋}`; previously only `m = 0, 1, 2` and
  `m = s + 1` were known.

## Main results

* `AdjSum.adjMatZ_mul_invAdjMatZ`, `AdjSum.invAdjMatZ_mul_adjMatZ` : `B` is a two-sided
  inverse of `A` over `ℤ`.
* `AdjSum.trace_invAdjMatZ` : `tr(A⁻¹) = (−1)^s`.
* `AdjSum.invAdjMatZ_sq` : `A⁻² = neumannLaplacian s`, a tridiagonal path Laplacian.
* `AdjSum.trace_invAdjMatZ_sq` : `tr(A⁻²) = 2s + 1`, i.e. `∑_t λ_t^{-2} = 2s+1`.
* `AdjSum.reverse_charpoly_adjMatZ` : `(charpoly A).reverse = (−1)^{s+1} det(A) · charpoly(A⁻¹)`.
* `AdjSum.charpoly_coeff_one_adjMatZ` : `coeff 1 of det(xI − A) = (−1)^{⌊(s+1)/2⌋}`.

-- !-- Lab Notes -- !--
* **Experiment.**  For `s = 3` the transfer matrix and its inverse are
  `A = [[1,1,1,1],[1,1,1,0],[1,1,0,0],[1,0,0,0]]`,
  `B = [[0,0,0,1],[0,0,1,-1],[0,1,-1,0],[1,-1,0,0]]`, and `B² = [[1,-1,0,0],[-1,2,-1,0],
  [0,-1,2,-1],[0,0,-1,2]]`.  The linear charpoly coefficients for `s = 0..9` are
  `-1, -1, 1, 1, -1, -1, 1, 1, -1, -1`, matching `(−1)^{⌊(s+1)/2⌋}` — note the sign
  convention: the coefficient of `x¹` sits at position `m = s`, so the prediction is
  `(−1)^{⌊(s+1)/2⌋}` only after the `(−1)^m` bookkeeping, which is what the theorem states.
* **Analysis.**  The inverse is *sparser* than the matrix itself, which is what makes the
  low-order coefficients of the charpoly (equivalently the high-order ones of the reversed
  charpoly) computable in closed form.  The identity `A⁻² = Laplacian` also gives the trace
  identity `∑_t 4 sin²((2t+1)π/(2(2s+3))) = 2s+1` for free.
* **Critique.**  Nothing here is definitional: `A · B = 1` is a genuine convolution
  identity whose two indicator sums telescope to `[a ≤ c] − [a < c]`, and the charpoly
  coefficient uses Mathlib's `reverse_charpoly` together with the unimodularity theorem.
-/

open AdjSum

open Finset Polynomial Matrix










/-! ### The reversed characteristic polynomial and the linear coefficient -/






lemma invAdjMatZ_apply (s : ℕ) (a b : Fin (s + 1)) :
    invAdjMatZ s a b = (if (a : ℕ) + (b : ℕ) = s then (1 : ℤ) else 0)
        - (if (a : ℕ) + (b : ℕ) = s + 1 then (1 : ℤ) else 0) := rfl

open AdjSum in
theorem solution(s : ℕ) : Matrix.trace (invAdjMatZ s) = (-1) ^ s := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, invAdjMatZ_apply]
  rw [Fin.sum_univ_eq_sum_range
    (fun a => (if a + a = s then (1 : ℤ) else 0) - (if a + a = s + 1 then (1 : ℤ) else 0)) (s + 1)]
  rcases Nat.even_or_odd s with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    have hcongr : ∀ a ∈ Finset.range (k + k + 1),
        (if a + a = k + k then (1 : ℤ) else 0) - (if a + a = k + k + 1 then (1 : ℤ) else 0)
          = if a = k then (1 : ℤ) else 0 := by
      intro a _
      split_ifs <;> omega
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq' (Finset.range (k + k + 1)) k
      (fun _ => (1 : ℤ)), if_pos (by simp)]
    exact (Even.neg_one_pow ⟨k, rfl⟩).symm
  · subst hk
    have hcongr : ∀ a ∈ Finset.range (2 * k + 1 + 1),
        (if a + a = 2 * k + 1 then (1 : ℤ) else 0)
            - (if a + a = 2 * k + 1 + 1 then (1 : ℤ) else 0)
          = if a = k + 1 then (-1 : ℤ) else 0 := by
      intro a _
      split_ifs <;> omega
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq' (Finset.range (2 * k + 1 + 1)) (k + 1)
      (fun _ => (-1 : ℤ)), if_pos (by simp; omega)]
    exact (Odd.neg_one_pow ⟨k, by ring⟩).symm
