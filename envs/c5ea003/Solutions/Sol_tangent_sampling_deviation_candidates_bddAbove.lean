-- Prove2me | solution 1 for tangent_sampling_deviation_candidates_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T14:36:13.936407+00:00
-- url     : https://prove2.me/submissions/9fae8550-831b-4b69-aa1d-f819e6893179

import Definitions.Def_matrix_completion_tangent

open scoped BigOperators
open MatrixCompletion
open Finset

namespace BddProof

variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

/-- Each entry is bounded by the Frobenius norm. -/
theorem entry_abs_le_frob (X : RealMatrix n1 n2) (i : Fin n1) (j : Fin n2) :
    |X i j| ≤ frobeniusNorm X := by
  have hsq : (X i j) ^ 2 ≤ frobeniusNormSq X := by
    unfold frobeniusNormSq
    have hnonneg : ∀ a ∈ (Finset.univ : Finset (Fin n1)),
        0 ≤ ∑ b : Fin n2, (X a b) ^ 2 := by
      intro a _; exact Finset.sum_nonneg (fun b _ => sq_nonneg _)
    have h1 : (X i j) ^ 2 ≤ ∑ b : Fin n2, (X i b) ^ 2 := by
      refine Finset.single_le_sum (f := fun b => (X i b) ^ 2) ?_ (Finset.mem_univ j)
      intro b _; exact sq_nonneg _
    have h2 : (∑ b : Fin n2, (X i b) ^ 2) ≤ ∑ a : Fin n1, ∑ b : Fin n2, (X a b) ^ 2 := by
      refine Finset.single_le_sum (f := fun a => ∑ b : Fin n2, (X a b) ^ 2) ?_ (Finset.mem_univ i)
      exact hnonneg
    exact le_trans h1 h2
  have habs : |X i j| = Real.sqrt ((X i j) ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
  rw [habs]
  unfold frobeniusNorm
  exact Real.sqrt_le_sqrt hsq

/-- If every entry of `Z` is bounded by `D ≥ 0`, the Frobenius norm is at most
`√(n1*n2)*D`. -/
theorem frob_le_of_entries (Z : RealMatrix n1 n2) (D : Real) (hD : 0 ≤ D)
    (hZ : ∀ i j, |Z i j| ≤ D) :
    frobeniusNorm Z ≤ Real.sqrt ((n1 : Real) * (n2 : Real)) * D := by
  have hsq : frobeniusNormSq Z ≤ (n1 : Real) * (n2 : Real) * D ^ 2 := by
    unfold frobeniusNormSq
    have hbound : ∀ i : Fin n1, (∑ j : Fin n2, (Z i j) ^ 2) ≤ (n2 : Real) * D ^ 2 := by
      intro i
      have : (∑ j : Fin n2, (Z i j) ^ 2) ≤ ∑ _j : Fin n2, D ^ 2 := by
        refine Finset.sum_le_sum ?_
        intro j _
        have := hZ i j
        have h2 : (Z i j) ^ 2 ≤ D ^ 2 := by
          have hb := hZ i j
          have : |Z i j| ^ 2 ≤ D ^ 2 := by
            apply pow_le_pow_left₀ (abs_nonneg _) hb
          rwa [sq_abs] at this
        exact h2
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_comm] using this
    calc (∑ i : Fin n1, ∑ j : Fin n2, (Z i j) ^ 2)
        ≤ ∑ _i : Fin n1, (n2 : Real) * D ^ 2 := Finset.sum_le_sum (fun i _ => hbound i)
      _ = (n1 : Real) * ((n2 : Real) * D ^ 2) := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (n1 : Real) * (n2 : Real) * D ^ 2 := by ring
  unfold frobeniusNorm
  have hrhs : Real.sqrt ((n1 : Real) * (n2 : Real) * D ^ 2)
      = Real.sqrt ((n1 : Real) * (n2 : Real)) * D := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hD]
  calc Real.sqrt (frobeniusNormSq Z)
      ≤ Real.sqrt ((n1 : Real) * (n2 : Real) * D ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt ((n1 : Real) * (n2 : Real)) * D := hrhs

/-- Explicit per-entry bound constant for the left singular projection. -/
noncomputable def CL (S : SVD M r) : Real :=
  ∑ i : Fin n1, ∑ a : Fin n1, |∑ k : Fin r, S.u k i * S.u k a|

noncomputable def CR (S : SVD M r) : Real :=
  ∑ j : Fin n2, ∑ b : Fin n2, |∑ k : Fin r, S.v k b * S.v k j|

noncomputable def CT (S : SVD M r) : Real :=
  ∑ i : Fin n1, ∑ j : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
    |(∑ k : Fin r, S.u k i * S.u k a)| * |(∑ l : Fin r, S.v l b * S.v l j)|

theorem CL_nonneg (S : SVD M r) : 0 ≤ CL S := by
  unfold CL; exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

theorem CR_nonneg (S : SVD M r) : 0 ≤ CR S := by
  unfold CR; exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

theorem CT_nonneg (S : SVD M r) : 0 ≤ CT S := by
  unfold CT
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))))

/-- Entry bound for the left singular projection when `|Y a b| ≤ 1`. -/
theorem left_entry_bound (S : SVD M r) (Y : RealMatrix n1 n2)
    (hY : ∀ a b, |Y a b| ≤ 1) (i : Fin n1) (j : Fin n2) :
    |leftSingularProjection S Y i j| ≤ CL S := by
  unfold leftSingularProjection
  have h1 : |∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * Y a j|
      ≤ ∑ a : Fin n1, |∑ k : Fin r, S.u k i * S.u k a| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum ?_
    intro a _
    rw [abs_mul]
    have : |Y a j| ≤ 1 := hY a j
    nlinarith [abs_nonneg (∑ k : Fin r, S.u k i * S.u k a), this, abs_nonneg (Y a j)]
  refine le_trans h1 ?_
  unfold CL
  refine Finset.single_le_sum (f := fun i' => ∑ a : Fin n1, |∑ k : Fin r, S.u k i' * S.u k a|) ?_ (Finset.mem_univ i)
  intro i' _; exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem right_entry_bound (S : SVD M r) (Y : RealMatrix n1 n2)
    (hY : ∀ a b, |Y a b| ≤ 1) (i : Fin n1) (j : Fin n2) :
    |rightSingularProjection S Y i j| ≤ CR S := by
  unfold rightSingularProjection
  have h1 : |∑ b : Fin n2, Y i b * (∑ k : Fin r, S.v k b * S.v k j)|
      ≤ ∑ b : Fin n2, |∑ k : Fin r, S.v k b * S.v k j| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum ?_
    intro b _
    rw [abs_mul]
    have : |Y i b| ≤ 1 := hY i b
    nlinarith [abs_nonneg (∑ k : Fin r, S.v k b * S.v k j), this, abs_nonneg (Y i b)]
  refine le_trans h1 ?_
  unfold CR
  refine Finset.single_le_sum (f := fun j' => ∑ b : Fin n2, |∑ k : Fin r, S.v k b * S.v k j'|) ?_ (Finset.mem_univ j)
  intro j' _; exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem twoSided_entry_bound (S : SVD M r) (Y : RealMatrix n1 n2)
    (hY : ∀ a b, |Y a b| ≤ 1) (i : Fin n1) (j : Fin n2) :
    |twoSidedSingularProjection S Y i j| ≤ CT S := by
  unfold twoSidedSingularProjection
  have h1 : |∑ a : Fin n1, ∑ b : Fin n2,
        (∑ k : Fin r, S.u k i * S.u k a) * Y a b * (∑ l : Fin r, S.v l b * S.v l j)|
      ≤ ∑ a : Fin n1, ∑ b : Fin n2,
          |(∑ k : Fin r, S.u k i * S.u k a)| * |(∑ l : Fin r, S.v l b * S.v l j)| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum ?_
    intro a _
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum ?_
    intro b _
    rw [abs_mul, abs_mul]
    have hyb : |Y a b| ≤ 1 := hY a b
    have hu := abs_nonneg (∑ k : Fin r, S.u k i * S.u k a)
    have hv := abs_nonneg (∑ l : Fin r, S.v l b * S.v l j)
    have hyn := abs_nonneg (Y a b)
    calc |∑ k : Fin r, S.u k i * S.u k a| * |Y a b| * |∑ l : Fin r, S.v l b * S.v l j|
        ≤ |∑ k : Fin r, S.u k i * S.u k a| * 1 * |∑ l : Fin r, S.v l b * S.v l j| := by
          apply mul_le_mul_of_nonneg_right _ hv
          exact mul_le_mul_of_nonneg_left hyb hu
      _ = |∑ k : Fin r, S.u k i * S.u k a| * |∑ l : Fin r, S.v l b * S.v l j| := by ring
  refine le_trans h1 ?_
  unfold CT
  -- term_{ij} ≤ ∑_{j'} term_{ij'} ≤ ∑_i ∑_{j'} term_{ij'}
  set term : Fin n1 → Fin n2 → Real :=
    fun i' j' => ∑ a : Fin n1, ∑ b : Fin n2,
      |(∑ k : Fin r, S.u k i' * S.u k a)| * |(∑ l : Fin r, S.v l b * S.v l j')| with hterm
  have hnonneg : ∀ i' j', 0 ≤ term i' j' := by
    intro i' j'
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity))
  have step1 : term i j ≤ ∑ j' : Fin n2, term i j' := by
    refine Finset.single_le_sum (f := fun j' => term i j') ?_ (Finset.mem_univ j)
    intro j' _; exact hnonneg i j'
  have step2 : (∑ j' : Fin n2, term i j') ≤ ∑ i' : Fin n1, ∑ j' : Fin n2, term i' j' := by
    refine Finset.single_le_sum (f := fun i' => ∑ j' : Fin n2, term i' j') ?_ (Finset.mem_univ i)
    intro i' _; exact Finset.sum_nonneg (fun j' _ => hnonneg i' j')
  exact le_trans step1 step2

/-- Per-entry bound on the full fluctuation `W = P_T(P_Ω X) - p•X` when
`frobeniusNorm X ≤ 1`. -/
theorem W_entry_bound (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : Real)
    (X : RealMatrix n1 n2) (hX : frobeniusNorm X ≤ 1) (i : Fin n1) (j : Fin n2) :
    |(tangentProjection S (samplingProjection Omega X) - p • X) i j|
      ≤ CL S + CR S + CT S + |p| := by
  set Y : RealMatrix n1 n2 := samplingProjection Omega X with hYdef
  have hYbound : ∀ a b, |Y a b| ≤ 1 := by
    intro a b
    rw [hYdef]
    unfold samplingProjection
    by_cases hab : (a, b) ∈ Omega
    · simp only [hab, if_true]
      exact le_trans (entry_abs_le_frob X a b) hX
    · simp only [hab, if_false, abs_zero]; norm_num
  -- entrywise expansion of the difference
  have hentry : (tangentProjection S Y - p • X) i j
      = leftSingularProjection S Y i j + rightSingularProjection S Y i j
        - twoSidedSingularProjection S Y i j - p * X i j := by
    unfold tangentProjection
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hentry]
  have hL := left_entry_bound S Y hYbound i j
  have hR := right_entry_bound S Y hYbound i j
  have hT := twoSided_entry_bound S Y hYbound i j
  have hpX : |p * X i j| ≤ |p| := by
    rw [abs_mul]
    have hxij : |X i j| ≤ 1 := le_trans (entry_abs_le_frob X i j) hX
    nlinarith [abs_nonneg p, abs_nonneg (X i j), hxij]
  set La := leftSingularProjection S Y i j
  set Ra := rightSingularProjection S Y i j
  set Ta := twoSidedSingularProjection S Y i j
  set Pa := p * X i j
  have htri : |La + Ra - Ta - Pa| ≤ |La| + |Ra| + |Ta| + |Pa| := by
    have e : La + Ra - Ta - Pa = La + (Ra + ((-Ta) + (-Pa))) := by ring
    rw [e]
    calc |La + (Ra + ((-Ta) + (-Pa)))|
        ≤ |La| + |Ra + ((-Ta) + (-Pa))| := abs_add_le _ _
      _ ≤ |La| + (|Ra| + |(-Ta) + (-Pa)|) := by gcongr; exact abs_add_le _ _
      _ ≤ |La| + (|Ra| + (|(-Ta)| + |(-Pa)|)) := by gcongr; exact abs_add_le _ _
      _ = |La| + |Ra| + |Ta| + |Pa| := by rw [abs_neg, abs_neg]; ring
  calc |La + Ra - Ta - Pa|
      ≤ |La| + |Ra| + |Ta| + |Pa| := htri
    _ ≤ CL S + CR S + CT S + |p| := by gcongr

end BddProof

open BddProof

theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    BddAbove {v : ℝ |
      ∃ X : Matrix (Fin n₁) (Fin n₂) ℝ,
        tangentProjection S X = X ∧ frobeniusNorm X ≤ 1 ∧
          v = (p⁻¹) *
            frobeniusNorm
              (tangentProjection S (samplingProjection Omega X) - p • X)} := by
  refine ⟨|p⁻¹| * (Real.sqrt ((n₁ : Real) * (n₂ : Real)) * (CL S + CR S + CT S + |p|)), ?_⟩
  rintro v ⟨X, _hXT, hXnorm, hv⟩
  set D : Real := CL S + CR S + CT S + |p| with hD
  have hDnonneg : 0 ≤ D := by
    rw [hD]; have := CL_nonneg S; have := CR_nonneg S; have := CT_nonneg S
    have := abs_nonneg p; linarith
  have hWbound : frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X)
      ≤ Real.sqrt ((n₁ : Real) * (n₂ : Real)) * D := by
    apply frob_le_of_entries _ D hDnonneg
    intro i j
    exact W_entry_bound S Omega p X hXnorm i j
  rw [hv]
  have hF : (0:Real) ≤ frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X) := by
    unfold frobeniusNorm; exact Real.sqrt_nonneg _
  calc (p⁻¹) * frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X)
      ≤ |p⁻¹| * frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X) := by
        have : p⁻¹ ≤ |p⁻¹| := le_abs_self _
        nlinarith [hF, this]
    _ ≤ |p⁻¹| * (Real.sqrt ((n₁ : Real) * (n₂ : Real)) * D) := by
        apply mul_le_mul_of_nonneg_left hWbound (abs_nonneg _)
