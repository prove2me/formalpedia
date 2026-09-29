-- Prove2me | solution 1 for max_degree_ge_lambda_max
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-05-01T02:00:54.174818+00:00
-- url     : https://prove2.me/submissions/2f46169c-6976-4502-aace-72c7a9ad5a85

import Theorems.Thm_max_degree_ge_lambda_max
import Mathlib.Data.Matrix.Mul

open Matrix

/-!
# Full proof — `max_degree_ge_lambda_max`

Standard "max-coordinate" Perron-style argument.  See the natural-language
sketch atop the proof.
-/

theorem solution
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℝ} (hA : A.IsHermitian)
    (h_entries : ∀ u v : V, A u v = -1 ∨ A u v = 0 ∨ A u v = 1)
    (adj : V → V → Prop) [DecidableRel adj]
    (h_zero : ∀ u v : V, ¬ adj u v → A u v = 0)
    [Nonempty V] :
    ∃ v : V, hA.eigenvalues₀ ⟨0, Fintype.card_pos⟩
      ≤ ((Finset.univ : Finset V).filter fun u => adj u v).card := by
  -- Bridge `eigenvalues₀ ⟨0, _⟩` to `eigenvalues j` for some `j : V`.
  set i0 : Fin (Fintype.card V) := ⟨0, Fintype.card_pos⟩
  set j : V := (Fintype.equivOfCardEq (Fintype.card_fin _)) i0 with hj_def
  have h_eig_bridge : hA.eigenvalues j = hA.eigenvalues₀ i0 := by
    show hA.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j) =
        hA.eigenvalues₀ i0
    congr 1
    rw [hj_def, Equiv.symm_apply_apply]
  set x : V → ℝ := ⇑(hA.eigenvectorBasis j) with hx_def
  set lam : ℝ := hA.eigenvalues j with hlam_def
  -- `A *ᵥ x = lam • x`.
  have hAv : A *ᵥ x = lam • x := hA.mulVec_eigenvectorBasis j
  -- `x ≠ 0`.
  have hx_ne : x ≠ 0 :=
    (WithLp.ofLp_eq_zero (p := 2)).ne.mpr
      (hA.eigenvectorBasis.orthonormal.ne_zero j)
  -- Max-coordinate index `i`.
  obtain ⟨i, _, hi_max⟩ :=
    (Finset.univ : Finset V).exists_max_image (fun k => |x k|) Finset.univ_nonempty
  -- `|x i| > 0`.
  have hxi_pos : 0 < |x i| := by
    by_contra h
    push_neg at h
    apply hx_ne
    funext k
    have hk : |x k| ≤ 0 := (hi_max k (Finset.mem_univ k)).trans h
    exact abs_eq_zero.mp (le_antisymm hk (abs_nonneg _))
  -- Eigenequation row `i`:  `lam * x i = ∑ k, A i k * x k`.
  have hrow : lam * x i = ∑ k, A i k * x k := by
    have hi := congrArg (fun f => f i) hAv
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi
    linarith
  -- Triangle + max-coord:  `|lam| * |x i| ≤ |x i| * ∑ k, |A i k|`.
  have hcomb : |lam| * |x i| ≤ |x i| * ∑ k, |A i k| := by
    have htri : |lam * x i| ≤ ∑ k, |A i k * x k| := by
      rw [hrow]; exact Finset.abs_sum_le_sum_abs _ _
    have hmax : ∑ k, |A i k * x k| ≤ |x i| * ∑ k, |A i k| := by
      calc ∑ k, |A i k * x k|
          ≤ ∑ k, |A i k| * |x i| := by
            apply Finset.sum_le_sum
            intro k _
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left
              (hi_max k (Finset.mem_univ k)) (abs_nonneg _)
        _ = (∑ k, |A i k|) * |x i| := (Finset.sum_mul _ _ _).symm
        _ = |x i| * ∑ k, |A i k| := mul_comm _ _
    calc |lam| * |x i|
        = |lam * x i| := (abs_mul _ _).symm
      _ ≤ ∑ k, |A i k * x k| := htri
      _ ≤ |x i| * ∑ k, |A i k| := hmax
  -- Cancel `|x i| > 0`:  `|lam| ≤ ∑ k, |A i k|`.
  have hlam_le_sum : |lam| ≤ ∑ k, |A i k| := by
    have hcomb' : |lam| * |x i| ≤ (∑ k, |A i k|) * |x i| := by
      rw [mul_comm (∑ k, |A i k|) |x i|]; exact hcomb
    exact le_of_mul_le_mul_right hcomb' hxi_pos
  -- `|A i k| = if A i k = 0 then 0 else 1`.
  have habs_eq : ∀ k, |A i k| = if A i k = 0 then 0 else 1 := by
    intro k
    rcases h_entries i k with h | h | h
    · rw [h]; simp
    · rw [h]; simp
    · rw [h]; simp
  -- `∑ k, |A i k| = ↑#{k : A i k ≠ 0}`.
  have hsum_eq_card : ∑ k, |A i k| =
      (((Finset.univ : Finset V).filter (fun k => A i k ≠ 0)).card : ℝ) := by
    rw [show (((Finset.univ : Finset V).filter (fun k => A i k ≠ 0)).card : ℝ)
          = ∑ _k ∈ ((Finset.univ : Finset V).filter (fun k => A i k ≠ 0)), (1 : ℝ)
        from by rw [Finset.sum_const, nsmul_eq_mul, mul_one]]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    rw [habs_eq k]
    by_cases h : A i k = 0 <;> simp [h]
  -- Hermiticity flip:  `A i k = A k i`.
  have hA_sym : ∀ k : V, A i k = A k i := fun k => by
    have h : star (A k i) = A i k := by
      have := congrArg (fun M : Matrix V V ℝ => M i k) hA
      simpa [Matrix.conjTranspose_apply] using this
    -- star = id on ℝ
    simpa using h.symm
  -- Reindex filter:  `{k : A i k ≠ 0} = {k : A k i ≠ 0}` as Finsets.
  have hfilter_eq :
      ((Finset.univ : Finset V).filter (fun k => A i k ≠ 0)) =
      ((Finset.univ : Finset V).filter (fun k => A k i ≠ 0)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h heq; exact h (by rw [hA_sym k]; exact heq)
    · intro h heq; exact h (by rw [← hA_sym k]; exact heq)
  -- `{k : A k i ≠ 0} ⊆ {k : adj k i}` (contrapositive of `h_zero`).
  have hcard_le :
      ((Finset.univ : Finset V).filter (fun k => A k i ≠ 0)).card ≤
      ((Finset.univ : Finset V).filter (fun u => adj u i)).card := by
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    by_contra hne
    exact hk (h_zero k i hne)
  -- Combine:  `|lam| ≤ #{u : adj u i}`.
  have hlam_le_card :
      |lam| ≤ (((Finset.univ : Finset V).filter (fun u => adj u i)).card : ℝ) := by
    calc |lam|
        ≤ ∑ k, |A i k| := hlam_le_sum
      _ = (((Finset.univ : Finset V).filter (fun k => A i k ≠ 0)).card : ℝ) := hsum_eq_card
      _ = (((Finset.univ : Finset V).filter (fun k => A k i ≠ 0)).card : ℝ) := by
          rw [hfilter_eq]
      _ ≤ (((Finset.univ : Finset V).filter (fun u => adj u i)).card : ℝ) := by
          exact_mod_cast hcard_le
  -- Conclude.
  refine ⟨i, ?_⟩
  rw [← h_eig_bridge]
  calc lam ≤ |lam| := le_abs_self _
    _ ≤ (((Finset.univ : Finset V).filter (fun u => adj u i)).card : ℝ) := hlam_le_card
