-- Prove2me | solution 1 for sign_matrix_inner_eq_nuclear_norm
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T21:31:04.287637+00:00
-- url     : https://prove2.me/submissions/1a452dd8-d0d3-4209-aa1b-0127e5fafcb2

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_svd
import Definitions.Def_matrix_completion_basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
L1 — `sign_matrix_inner_eq_nuclear_norm`:  `⟨E, M⟩ = ‖M‖_*`  (Candès–Recht 2009, eq.(3.3), p.15).
Easy half (orthonormality):  `⟨E, M⟩ = ∑_k σ_k`.
Deep half (SVD uniqueness):  `∑_k σ_k = nuclearNorm M` (eigenvalue-multiset / charpoly argument).
-/

namespace MatrixCompletion

open scoped Classical BigOperators
open Matrix LinearMap Module InnerProductSpace Polynomial WithLp

variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

open scoped Classical BigOperators
open Matrix LinearMap Module InnerProductSpace Polynomial WithLp

variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

/-- The Gram matrix `Mᵀ * M`. -/
noncomputable abbrev gramMat (M : RealMatrix n1 n2) : Matrix (Fin n2) (Fin n2) ℝ := Mᵀ * M

/-- `Mᵀ M = ∑_k σ_k² • (v_k v_kᵀ)` (using orthonormality of the left vectors `u`). -/
theorem gramMat_eq_sum (S : SVD M r) :
    gramMat M = ∑ k, (S.sigma k ^ 2) • Matrix.vecMulVec (S.v k) (S.v k) := by
  ext a b
  -- entrywise:  (Mᵀ M) a b = ∑_i M i a * M i b
  show (Mᵀ * M) a b = _
  rw [Matrix.mul_apply]
  have hMia : ∀ i a, M i a = ∑ l, S.sigma l * (S.u l i * S.v l a) := by
    intro i a
    have := congrFun (congrFun S.decomp i) a
    rw [this]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  -- RHS entry
  have hRHS : (∑ k, (S.sigma k ^ 2) • Matrix.vecMulVec (S.v k) (S.v k)) a b
      = ∑ k, (S.sigma k ^ 2) * (S.v k a * S.v k b) := by
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [hRHS]
  -- expand LHS
  have hLHS : (∑ i, Mᵀ a i * M i b) = ∑ i, M i a * M i b := by
    apply Finset.sum_congr rfl; intro i _; rw [Matrix.transpose_apply]
  rw [hLHS]
  calc (∑ i, M i a * M i b)
      = ∑ i, (∑ l, S.sigma l * (S.u l i * S.v l a)) * (∑ m, S.sigma m * (S.u m i * S.v m b)) := by
        apply Finset.sum_congr rfl; intro i _; rw [hMia i a, hMia i b]
    _ = ∑ i, ∑ l, ∑ m,
          (S.sigma l * S.sigma m) * (S.v l a * S.v m b) * (S.u l i * S.u m i) := by
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.sum_mul_sum]
        apply Finset.sum_congr rfl; intro l _
        apply Finset.sum_congr rfl; intro m _
        ring
    _ = ∑ l, ∑ m, (S.sigma l * S.sigma m) * (S.v l a * S.v m b) * (∑ i, S.u l i * S.u m i) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro l _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro m _
        rw [Finset.mul_sum]
    _ = ∑ l, (S.sigma l ^ 2) * (S.v l a * S.v l b) := by
        apply Finset.sum_congr rfl; intro l _
        rw [Finset.sum_eq_single l]
        · rw [S.u_orthonormal l l, if_pos rfl]; ring
        · intro m _ hml
          rw [S.u_orthonormal l m, if_neg (fun h => hml h.symm)]; ring
        · intro h; exact absurd (Finset.mem_univ l) h

/-! ## Operator-level setup. -/

/-- `T = toEuclideanLin M`. -/
noncomputable abbrev Top (M : RealMatrix n1 n2) : EuclideanSpace ℝ (Fin n2) →ₗ[ℝ] EuclideanSpace ℝ (Fin n1) :=
  Matrix.toEuclideanLin M

/-- `G = adjoint T ∘ₗ T`, the Gram operator. -/
noncomputable abbrev Gop (M : RealMatrix n1 n2) : EuclideanSpace ℝ (Fin n2) →ₗ[ℝ] EuclideanSpace ℝ (Fin n2) :=
  LinearMap.adjoint (Top M) ∘ₗ (Top M)

theorem Gop_symm (M : RealMatrix n1 n2) : (Gop M).IsSymmetric :=
  (Top M).isSymmetric_adjoint_comp_self

/-- `G = toEuclideanLin (Mᵀ M)`. -/
theorem Gop_eq_toEuclideanLin (M : RealMatrix n1 n2) :
    Gop M = Matrix.toEuclideanLin (Mᵀ * M) := by
  have hadj : LinearMap.adjoint (Top M) = Matrix.toEuclideanLin Mᵀ := by
    have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint (M)
    rw [show Mᵀ = Mᴴ from ?_]
    · exact h.symm
    · ext i j; simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, hadj]
  -- toEuclideanLin Mᵀ (toEuclideanLin M x) = toEuclideanLin (Mᵀ * M) x
  apply (WithLp.equiv 2 (Fin n2 → ℝ)).injective
  simp only [WithLp.equiv_apply]
  rw [Matrix.ofLp_toEuclideanLin_apply, Matrix.ofLp_toEuclideanLin_apply,
    Matrix.ofLp_toEuclideanLin_apply, Matrix.mulVec_mulVec]

/-- The right singular vector `vv k` as a point of Euclidean space. -/
noncomputable def vv (S : SVD M r) (k : Fin r) : EuclideanSpace ℝ (Fin n2) :=
  toLp 2 (S.v k)

theorem vv_ofLp (S : SVD M r) (k : Fin r) : ofLp (vv S k) = S.v k := rfl

/-- Orthonormality of the `vv k` in EuclideanSpace. -/
theorem vv_orthonormal (S : SVD M r) : Orthonormal ℝ (vv S) := by
  rw [orthonormal_iff_ite]
  intro k l
  rw [PiLp.inner_apply]
  simp only [vv, WithLp.ofLp_toLp]
  have := S.v_orthonormal k l
  rw [show (∑ x, (inner ℝ (S.v k x) (S.v l x)) ) = ∑ j, S.v k j * S.v l j from
    Finset.sum_congr rfl (fun x _ => by rw [show (inner ℝ (S.v k x) (S.v l x) : ℝ)
      = S.v l x * S.v k x from rfl, mul_comm])]
  rw [this]

/-- The matrix eigenvalue equation `(Mᵀ M) *ᵥ v_k = σ_k² • v_k`. -/
theorem gramMat_mulVec_v (S : SVD M r) (k : Fin r) :
    (Mᵀ * M) *ᵥ S.v k = (S.sigma k ^ 2) • S.v k := by
  have hg : (Mᵀ * M) = ∑ l, (S.sigma l ^ 2) • Matrix.vecMulVec (S.v l) (S.v l) :=
    gramMat_eq_sum S
  rw [hg]
  funext a
  simp only [Matrix.mulVec, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.smul_apply, smul_eq_mul, dotProduct]
  -- ∑_b (∑_l σ_l² v_l a v_l b) v_k b = σ_k² v_k a
  rw [show (∑ b, (∑ l, S.sigma l ^ 2 * (S.v l a * S.v l b)) * S.v k b)
        = ∑ l, S.sigma l ^ 2 * S.v l a * (∑ b, S.v l b * S.v k b) from ?_]
  · rw [Finset.sum_eq_single k]
    · rw [S.v_orthonormal k k, if_pos rfl]; ring
    · intro l _ hlk
      rw [S.v_orthonormal l k, if_neg hlk]; ring
    · intro h; exact absurd (Finset.mem_univ k) h
  · have step1 : (∑ b, (∑ l, S.sigma l ^ 2 * (S.v l a * S.v l b)) * S.v k b)
          = ∑ b, ∑ l, (S.sigma l ^ 2 * S.v l a) * (S.v l b * S.v k b) := by
      apply Finset.sum_congr rfl; intro b _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro l _; ring
    rw [step1, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]

/-- Eigenvector equation:  `G (vv k) = σ_k² • vv k`. -/
theorem Gop_vv (S : SVD M r) (k : Fin r) :
    Gop M (vv S k) = (S.sigma k ^ 2) • vv S k := by
  rw [Gop_eq_toEuclideanLin]
  apply (WithLp.equiv 2 (Fin n2 → ℝ)).injective
  simp only [WithLp.equiv_apply]
  rw [Matrix.ofLp_toEuclideanLin_apply, vv_ofLp, WithLp.ofLp_smul, vv_ofLp,
    gramMat_mulVec_v S k]

/-- The real inner `⟪vv_k, x⟫ = ∑_b v_k b · (ofLp x) b`. -/
theorem inner_vv (S : SVD M r) (k : Fin r) (x : EuclideanSpace ℝ (Fin n2)) :
    (inner ℝ (vv S k) x : ℝ) = ∑ b, S.v k b * (ofLp x) b := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl; intro b _
  rw [show (inner ℝ ((ofLp (vv S k)) b) ((ofLp x) b) : ℝ) = (ofLp x) b * (ofLp (vv S k)) b from rfl,
    vv_ofLp]
  ring

/-- Operator form of the Gram operator: `G x = ∑_k σ_k² ⟪vv_k, x⟫ vv_k`. -/
theorem Gop_apply_eq_sum (S : SVD M r) (x : EuclideanSpace ℝ (Fin n2)) :
    Gop M x = ∑ k, (S.sigma k ^ 2 * (inner ℝ (vv S k) x)) • vv S k := by
  rw [Gop_eq_toEuclideanLin]
  apply (WithLp.equiv 2 (Fin n2 → ℝ)).injective
  simp only [WithLp.equiv_apply]
  have hg : (Mᵀ * M) = ∑ l, (S.sigma l ^ 2) • Matrix.vecMulVec (S.v l) (S.v l) :=
    gramMat_eq_sum S
  rw [Matrix.ofLp_toEuclideanLin_apply, hg, WithLp.ofLp_sum]
  funext a
  rw [Matrix.sum_mulVec, Finset.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl; intro k _
  rw [WithLp.ofLp_smul]
  simp only [Matrix.mulVec, Matrix.smul_apply, Matrix.vecMulVec_apply, dotProduct,
    Pi.smul_apply, smul_eq_mul]
  rw [inner_vv S k x, vv_ofLp, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro b _
  ring

/-! ## Eigenbasis construction. -/

theorem r_le_n2 (S : SVD M r) : r ≤ n2 := by
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2 := finrank_euclideanSpace_fin
  have hli := (vv_orthonormal S).linearIndependent
  have := hli.fintype_card_le_finrank (M := EuclideanSpace ℝ (Fin n2))
  simpa [hfin] using this

/-- Inclusion `Fin r ↪ Fin n2`. -/
noncomputable def incl (S : SVD M r) : Fin r → Fin n2 := fun k => Fin.castLE (r_le_n2 S) k

theorem incl_injective (S : SVD M r) : Function.Injective (incl S) := by
  intro a b h
  exact Fin.castLE_injective (r_le_n2 S) h

/-- The total extension of `vv` to `Fin n2 → E` (junk `0` off the range). -/
noncomputable def vext (S : SVD M r) : Fin n2 → EuclideanSpace ℝ (Fin n2) :=
  Function.extend (incl S) (vv S) 0

theorem vext_incl (S : SVD M r) (k : Fin r) : vext S (incl S k) = vv S k := by
  unfold vext
  rw [(incl_injective S).extend_apply]

theorem vext_orthonormal_restrict (S : SVD M r) :
    Orthonormal ℝ ((Set.range (incl S)).restrict (vext S)) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i, hi⟩ ⟨j, hj⟩
  obtain ⟨ki, rfl⟩ := hi
  obtain ⟨kj, rfl⟩ := hj
  simp only [Set.restrict_apply, vext_incl]
  rw [orthonormal_iff_ite.mp (vv_orthonormal S) ki kj]
  have hiff : (⟨incl S ki, Set.mem_range_self ki⟩ : Set.range (incl S))
      = ⟨incl S kj, Set.mem_range_self kj⟩ ↔ ki = kj := by
    rw [Subtype.ext_iff]
    constructor
    · intro h; exact incl_injective S h
    · intro h; rw [h]
  by_cases h : ki = kj
  · subst h; simp
  · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]

/-- The extended orthonormal basis whose first `r` vectors are the `vv k`. -/
noncomputable def bb (S : SVD M r) : OrthonormalBasis (Fin n2) ℝ (EuclideanSpace ℝ (Fin n2)) :=
  (vext_orthonormal_restrict S).exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace_fin, Fintype.card_fin]) |>.choose

theorem bb_spec (S : SVD M r) : ∀ i ∈ Set.range (incl S), bb S i = vext S i :=
  (vext_orthonormal_restrict S).exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace_fin, Fintype.card_fin]) |>.choose_spec

theorem bb_incl (S : SVD M r) (k : Fin r) : bb S (incl S k) = vv S k := by
  rw [bb_spec S (incl S k) (Set.mem_range_self k), vext_incl]

/-- The diagonal eigenvalue function: `σ_k²` on `incl k`, `0` elsewhere. -/
noncomputable def dvec (S : SVD M r) : Fin n2 → ℝ :=
  fun i => if h : ∃ k, incl S k = i then S.sigma h.choose ^ 2 else 0

theorem dvec_incl (S : SVD M r) (k : Fin r) : dvec S (incl S k) = S.sigma k ^ 2 := by
  unfold dvec
  have hex : ∃ k', incl S k' = incl S k := ⟨k, rfl⟩
  rw [dif_pos hex]
  have : hex.choose = k := incl_injective S hex.choose_spec
  rw [this]

theorem dvec_not_range (S : SVD M r) (i : Fin n2) (hi : ¬ ∃ k, incl S k = i) :
    dvec S i = 0 := by
  unfold dvec; rw [dif_neg hi]

/-- `bb i` for `i` outside the range of `incl` is orthogonal to every `vv k`. -/
theorem bb_orthogonal_vv (S : SVD M r) (i : Fin n2) (hi : ¬ ∃ k, incl S k = i) (k : Fin r) :
    (inner ℝ (vv S k) (bb S i) : ℝ) = 0 := by
  rw [← bb_incl S k]
  have hne : incl S k ≠ i := fun h => hi ⟨k, h⟩
  have := (bb S).orthonormal
  rw [orthonormal_iff_ite] at this
  rw [this (incl S k) i, if_neg hne]

/-- Key eigen-equation in the extended basis: `G (bb i) = dvec i • bb i`. -/
theorem Gop_bb (S : SVD M r) (i : Fin n2) :
    Gop M (bb S i) = dvec S i • bb S i := by
  by_cases hi : ∃ k, incl S k = i
  · obtain ⟨k, rfl⟩ := hi
    rw [bb_incl, Gop_vv, dvec_incl]
  · -- i outside range: G (bb i) = 0 and dvec i = 0
    rw [dvec_not_range S i hi, zero_smul]
    rw [Gop_apply_eq_sum S]
    apply Finset.sum_eq_zero
    intro k _
    rw [bb_orthogonal_vv S i hi k, mul_zero, zero_smul]

/-! ## Charpoly and the eigenvalue multiset. -/

/-- `G` is diagonal (with diagonal `dvec`) in the basis `bb`. -/
theorem toMatrix_bb_diagonal (S : SVD M r) :
    LinearMap.toMatrix (bb S).toBasis (bb S).toBasis (Gop M) = Matrix.diagonal (dvec S) := by
  ext i j
  rw [LinearMap.toMatrix_apply, (bb S).coe_toBasis, Gop_bb S j, map_smul, Finsupp.smul_apply,
    (bb S).coe_toBasis_repr_apply, (bb S).repr_self, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [EuclideanSpace.single_apply, if_neg h, if_neg h, smul_zero]

/-- `charpoly G = ∏_i (X - C (dvec i))`. -/
theorem charpoly_Gop (S : SVD M r) :
    (Gop M).charpoly = ∏ i, (Polynomial.X - Polynomial.C (dvec S i)) := by
  rw [← (Gop M).charpoly_toMatrix (bb S).toBasis, toMatrix_bb_diagonal S,
    Matrix.charpoly_diagonal]

/-! ## The eigenvalue multiset equals the `dvec` multiset, and the final sum. -/

/-- The multiset of `dvec` values equals the multiset of `G`-eigenvalues. -/
theorem eigenvalues_multiset_eq (S : SVD M r) (hn : finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2) :
    (Finset.univ.val.map ((Gop_symm M).eigenvalues hn))
      = Finset.univ.val.map (dvec S) := by
  -- both equal (charpoly G).roots (as ℝ-multisets, since RCLike.ofReal = id over ℝ)
  have hroots_g := (Gop_symm M).roots_charpoly_eq_eigenvalues hn
  have hcp := charpoly_Gop S
  -- roots of ∏(X - C dvec i)
  have hprod : (∏ i, (Polynomial.X - Polynomial.C (dvec S i)))
      = ((Finset.univ.val.map (dvec S)).map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.map_map]
    rw [Finset.prod_eq_multiset_prod]
    rfl
  have hroots_d : (Gop M).charpoly.roots = Finset.univ.val.map (dvec S) := by
    rw [hcp, hprod, Polynomial.roots_multiset_prod_X_sub_C]
  -- combine; ofReal over ℝ is the identity
  rw [hroots_d] at hroots_g
  -- hroots_g : univ.val.map dvec = univ.val.map (ofReal ∘ eigenvalues G)
  rw [hroots_g]
  apply Multiset.map_congr rfl
  intro x _
  simp [Function.comp]

/-- THE TARGET (SVD uniqueness): `∑_k σ_k = nuclearNorm M`. -/
theorem svd_sigma_sum_eq_nuclearNorm (S : SVD M r) :
    ∑ k, S.sigma k = nuclearNorm M := by
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2 := finrank_euclideanSpace_fin
  set T := Matrix.toEuclideanLin M with hT
  -- Step A: nuclearNorm M = ∑_{i:Fin n2} singularValues T i
  have hnuc : nuclearNorm M = ∑ i : Fin n2, T.singularValues i := by
    unfold nuclearNorm
    rw [← hT]
    rw [Finsupp.sum_of_support_subset T.singularValues
        (s := Finset.range n2) ?_ (fun _ x => x) (by intro _ _; rfl)]
    · rw [Finset.sum_range fun k => T.singularValues k]
    · intro k hk
      rw [Finset.mem_range]
      by_contra hge
      push_neg at hge
      have : T.singularValues k = 0 := by
        apply T.singularValues_of_finrank_le; rw [hn]; exact hge
      rw [Finsupp.mem_support_iff] at hk; exact hk this
  -- Step B: singularValues T i = √(eigenvalues G i)
  have hsv : ∀ i : Fin n2, T.singularValues i = Real.sqrt ((Gop_symm M).eigenvalues hn i) := by
    intro i
    rw [T.singularValues_fin hn i]
  rw [hnuc]
  -- ∑ singularValues T i = ∑ √(eigenvalues G i)
  rw [show (∑ i : Fin n2, T.singularValues i)
      = ∑ i : Fin n2, Real.sqrt ((Gop_symm M).eigenvalues hn i) from
    Finset.sum_congr rfl (fun i _ => hsv i)]
  -- Convert finite sums to multiset sums and use the multiset equality
  have hconv1 : (∑ i : Fin n2, Real.sqrt ((Gop_symm M).eigenvalues hn i))
        = ((Finset.univ.val.map ((Gop_symm M).eigenvalues hn)).map Real.sqrt).sum := by
    rw [Multiset.map_map]; rfl
  have hconv2 : ((Finset.univ.val.map (dvec S)).map Real.sqrt).sum
        = ∑ i : Fin n2, Real.sqrt (dvec S i) := by
    rw [Multiset.map_map]; rfl
  rw [hconv1, eigenvalues_multiset_eq S hn, hconv2]
  -- ∑_{i:Fin n2} √(dvec i) = ∑_k σ_k  (off-range terms vanish, on-range √(σ_k²)=σ_k)
  rw [show (∑ i : Fin n2, Real.sqrt (dvec S i))
        = ∑ k : Fin r, Real.sqrt (dvec S (incl S k)) from ?_]
  · refine (Finset.sum_congr rfl (fun k _ => ?_)).symm
    rw [dvec_incl, Real.sqrt_sq (le_of_lt (S.sigma_pos k))]
  · -- off-range vanish
    rw [← Finset.sum_image (f := fun i => Real.sqrt (dvec S i)) (g := incl S)
      (by intro a _ b _ h; exact incl_injective S h)]
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro i _ hi
    -- i ∉ image incl univ  ⇒  i ∉ range incl  ⇒  dvec i = 0
    rw [dvec_not_range S i ?_, Real.sqrt_zero]
    rintro ⟨k, rfl⟩
    exact hi (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)



open scoped Classical BigOperators


/-- Reorder a 4-fold finite sum, pulling the inner pair of indices `(k,l)` out. -/
theorem sum4_reorder {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  have hL : (∑ i, ∑ j, ∑ k, ∑ l, f i j k l)
      = ∑ p : α × β, ∑ q : γ × δ, f p.1 p.2 q.1 q.2 := by
    rw [← Fintype.sum_prod_type' (fun (i : α) (j : β) => ∑ k, ∑ l, f i j k l)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Fintype.sum_prod_type' (fun (k : γ) (l : δ) => f p.1 p.2 k l)]
  have hR : (∑ k, ∑ l, ∑ i, ∑ j, f i j k l)
      = ∑ q : γ × δ, ∑ p : α × β, f p.1 p.2 q.1 q.2 := by
    rw [← Fintype.sum_prod_type' (fun (k : γ) (l : δ) => ∑ i, ∑ j, f i j k l)]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [← Fintype.sum_prod_type' (fun (i : α) (j : β) => f i j q.1 q.2)]
  rw [hL, hR, Finset.sum_comm]

/-- EASY half of L1: the sign matrix inner product with `M` is the sum of the
SVD singular values, by orthonormality of the singular vectors. -/
theorem signMatrix_inner_eq_sum_sigma (S : SVD M r) :
    matrixInner (signMatrix S) M = ∑ k, S.sigma k := by
  unfold matrixInner
  -- entry-wise SVD expansion of M (real equation, no motive problem)
  have hMij : ∀ i j, M i j = ∑ l, S.sigma l * (S.u l i * S.v l j) := by
    intro i j
    have := congrFun (congrFun S.decomp i) j
    rw [this]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  have hEij : ∀ i j, (signMatrix S) i j = ∑ k, S.u k i * S.v k j := by
    intro i j
    unfold signMatrix
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply]
  have hentry : ∀ i j,
      (signMatrix S) i j * M i j
        = ∑ k, ∑ l, (S.sigma l) * (S.u k i * S.u l i) * (S.v k j * S.v l j) := by
    intro i j
    rw [hEij i j, hMij i j, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _
    ring
  calc (∑ i, ∑ j, (signMatrix S) i j * M i j)
      = ∑ i, ∑ j, ∑ k, ∑ l, (S.sigma l) * (S.u k i * S.u l i) * (S.v k j * S.v l j) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        rw [hentry i j]
    _ = ∑ k, ∑ l, ∑ i, ∑ j,
          (S.sigma l) * (S.u k i * S.u l i) * (S.v k j * S.v l j) :=
        sum4_reorder (fun i j k l => (S.sigma l) * (S.u k i * S.u l i) * (S.v k j * S.v l j))
    _ = ∑ k, ∑ l, (S.sigma l) *
          ((∑ i, S.u k i * S.u l i) * (∑ j, S.v k j * S.v l j)) := by
        refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
    _ = ∑ k, S.sigma k := by
        apply Finset.sum_congr rfl; intro k _
        rw [Finset.sum_eq_single k]
        · rw [S.u_orthonormal k k, S.v_orthonormal k k]; simp
        · intro l _ hlk
          rw [S.u_orthonormal k l]
          rw [if_neg (fun h => hlk h.symm)]
          ring
        · intro h; exact absurd (Finset.mem_univ k) h

end MatrixCompletion

open MatrixCompletion

/-- L1 — the sign matrix realizes the nuclear norm (Candès–Recht 2009, eq.(3.3)). -/
theorem solution {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r) :
    matrixInner (signMatrix S) M = nuclearNorm M := by
  rw [signMatrix_inner_eq_sum_sigma S, svd_sigma_sum_eq_nuclearNorm S]
