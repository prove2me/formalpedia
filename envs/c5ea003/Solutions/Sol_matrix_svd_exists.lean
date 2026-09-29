-- Prove2me | solution 1 for matrix_svd_exists
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T22:03:53.28202+00:00
-- url     : https://prove2.me/submissions/21405450-69ef-41a1-ab30-b50c884b97a7

import Definitions.Def_matrix_completion_svd
import Definitions.Def_matrix_completion_basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace


/-!
Operator-level SVD reconstruction probe.

For a linear map `T : E →ₗ[ℝ] F` between finite-dimensional real inner product
spaces, we build:
  v_k = eigenvectorBasis of G = adjoint T ∘ₗ T (orthonormal, eigenvalues μ_k ≥ 0)
  σ_k = √μ_k = singularValues T k
  reconstruction  T x = ∑_k σ_k • ⟪v_k, x⟫ • u_k   where u_k = σ_k⁻¹ • T v_k.
We first prove the cleanest invariant form:
  T x = ∑_k ⟪v_k, x⟫ • T v_k   (just sum_repr' + linearity),
then  ‖T v_k‖ = σ_k  and the orthogonality of {T v_k}.
-/

open Module InnerProductSpace LinearMap
open scoped BigOperators

namespace SVDProbe

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

noncomputable abbrev gram (T : E →ₗ[ℝ] F) : E →ₗ[ℝ] E := adjoint T ∘ₗ T

theorem gram_symm (T : E →ₗ[ℝ] F) : (gram T).IsSymmetric :=
  T.isSymmetric_adjoint_comp_self

theorem gram_pos (T : E →ₗ[ℝ] F) : (gram T).IsPositive :=
  T.isPositive_adjoint_comp_self

-- right singular vectors: orthonormal eigenbasis of G
noncomputable def rsv (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) :
    OrthonormalBasis (Fin n) ℝ E :=
  (gram_symm T).eigenvectorBasis hn

noncomputable def evals (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) : Fin n → ℝ :=
  (gram_symm T).eigenvalues hn

theorem evals_nonneg (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    0 ≤ evals T hn k :=
  (gram_pos T).nonneg_eigenvalues hn k

-- Reconstruction of T from the right singular vectors.
theorem recon (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (x : E) :
    T x = ∑ k, (inner ℝ (rsv T hn k) x) • T (rsv T hn k) := by
  conv_lhs => rw [← (rsv T hn).sum_repr' x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul]

-- Key Gram identity: ⟪T v_i, T v_j⟫ = ⟪G v_i, v_j⟫.
theorem inner_Tv (T : E →ₗ[ℝ] F) (a b : E) :
    inner ℝ (T a) (T b) = inner ℝ (gram T a) b := by
  unfold gram
  rw [LinearMap.comp_apply, ← LinearMap.adjoint_inner_left]

-- ⟪T v_i, T v_j⟫ = μ_i δ_ij.
theorem inner_Tv_eig (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (i j : Fin n) :
    inner ℝ (T (rsv T hn i)) (T (rsv T hn j))
      = if i = j then evals T hn i else 0 := by
  rw [inner_Tv]
  unfold gram rsv evals
  rw [show (adjoint T ∘ₗ T) ((gram_symm T).eigenvectorBasis hn i)
        = (gram T) ((gram_symm T).eigenvectorBasis hn i) from rfl]
  rw [(gram_symm T).apply_eigenvectorBasis hn i]
  rw [inner_smul_left]
  rw [orthonormal_iff_ite.mp ((gram_symm T).eigenvectorBasis hn).orthonormal i j]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

noncomputable def sval (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) : ℝ :=
  T.singularValues k

theorem sval_nonneg (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    0 ≤ sval T hn k := T.singularValues_nonneg k

theorem sval_sq (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    sval T hn k ^ 2 = evals T hn k := by
  unfold sval evals
  rw [T.sq_singularValues_fin hn k]

-- ‖T v_k‖ = σ_k.
theorem norm_Tv (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    ‖T (rsv T hn k)‖ = sval T hn k := by
  have h2 : ‖T (rsv T hn k)‖ ^ 2 = sval T hn k ^ 2 := by
    rw [@norm_sq_eq_re_inner ℝ]
    have := inner_Tv_eig T hn k k
    simp only [if_pos rfl] at this
    rw [this, sval_sq]
    simp
  have hnn := sval_nonneg T hn k
  nlinarith [norm_nonneg (T (rsv T hn k)), h2, hnn]

-- T v_k as σ_k times a unit left-singular vector (only meaningful when σ_k>0;
-- when σ_k=0, T v_k = 0).
theorem Tv_zero_of_sval_zero (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n)
    (h : sval T hn k = 0) : T (rsv T hn k) = 0 := by
  have := norm_Tv T hn k
  rw [h] at this
  exact norm_eq_zero.mp this

/-! ## Hilbert–Schmidt inner product, basis-independent. -/

-- ∑_j ⟪S b_j, T b_j⟫ = trace (adjoint S ∘ T), basis-independent.
theorem hsInner_eq_trace {ι : Type*} [Fintype ι] (S T : E →ₗ[ℝ] F) (b : OrthonormalBasis ι ℝ E) :
    (∑ j, inner ℝ (S (b j)) (T (b j))) = (adjoint S ∘ₗ T).trace ℝ E := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro j _
  rw [LinearMap.comp_apply, ← LinearMap.adjoint_inner_right S (b j) (T (b j))]

-- Therefore HS inner over the standard basis = HS inner over the eigenbasis.
theorem hsInner_basis_indep {ι : Type*} [Fintype ι] (S T : E →ₗ[ℝ] F)
    (b : OrthonormalBasis ι ℝ E) {n : ℕ} (hn : finrank ℝ E = n) :
    (∑ j, inner ℝ (S (b j)) (T (b j)))
      = ∑ k, inner ℝ (S (rsv T hn k)) (T (rsv T hn k)) := by
  rw [hsInner_eq_trace S T b, hsInner_eq_trace S T (rsv T hn)]

/-! ## Operator-level von Neumann trace inequality.
    ∑_j ⟪S b_j, T b_j⟫ ≤ ‖S‖ · ∑_k σ_k(T). -/

theorem vonNeumann_op {ι : Type*} [Fintype ι] (S : E →L[ℝ] F) (T : E →ₗ[ℝ] F)
    (b : OrthonormalBasis ι ℝ E) {n : ℕ} (hn : finrank ℝ E = n) :
    (∑ j, inner ℝ ((S : E →ₗ[ℝ] F) (b j)) (T (b j))) ≤ ‖S‖ * ∑ k, sval T hn k := by
  rw [hsInner_basis_indep (S : E →ₗ[ℝ] F) T b hn]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  -- ⟪S v_k, T v_k⟫ ≤ ‖S v_k‖ ‖T v_k‖ ≤ ‖S‖ ‖v_k‖ σ_k = ‖S‖ σ_k
  have hSle : ‖(S : E →ₗ[ℝ] F) (rsv T hn k)‖ ≤ ‖S‖ * ‖(rsv T hn k : E)‖ := S.le_opNorm _
  calc inner ℝ ((S : E →ₗ[ℝ] F) (rsv T hn k)) (T (rsv T hn k))
      ≤ ‖(S : E →ₗ[ℝ] F) (rsv T hn k)‖ * ‖T (rsv T hn k)‖ := real_inner_le_norm _ _
    _ ≤ (‖S‖ * ‖(rsv T hn k : E)‖) * ‖T (rsv T hn k)‖ := by
          apply mul_le_mul_of_nonneg_right hSle (norm_nonneg _)
    _ = ‖S‖ * sval T hn k := by
          rw [(rsv T hn).orthonormal.1 k, norm_Tv]; ring

end SVDProbe

namespace MatrixCompletion
open scoped Classical BigOperators
open Module InnerProductSpace LinearMap Matrix WithLp SVDProbe

theorem _svd_exists_aux {n1 n2 : Nat} (N : RealMatrix n1 n2) :
    ∃ (r : Nat) (S : SVD N r), True := by
  set T : EuclideanSpace ℝ (Fin n2) →ₗ[ℝ] EuclideanSpace ℝ (Fin n1) :=
    Matrix.toEuclideanLin N with hT
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2 := finrank_euclideanSpace_fin
  set b := rsv T hn with hb
  -- the set of indices with positive singular value
  set P : Finset (Fin n2) := Finset.univ.filter (fun k => 0 < sval T hn k) with hP
  set r : Nat := P.card with hr
  -- equiv between Fin r and P
  set e : Fin r ≃ {x // x ∈ P} := P.equivFin.symm with he
  set idx : Fin r → Fin n2 := fun k => (e k : Fin n2) with hidx
  have hidx_mem : ∀ k, idx k ∈ P := fun k => (e k).2
  have hidx_pos : ∀ k, 0 < sval T hn (idx k) := by
    intro k
    have := hidx_mem k
    rw [hP, Finset.mem_filter] at this
    exact this.2
  have hidx_inj : Function.Injective idx := by
    intro a c h
    apply e.injective
    apply Subtype.ext
    simpa [hidx] using h
  -- definitions of the SVD data
  set sigma : Fin r → ℝ := fun k => sval T hn (idx k) with hsigma
  set vvec : Fin r → (Fin n2 → ℝ) := fun k => ofLp (b (idx k)) with hvvec
  set uvec : Fin r → (Fin n1 → ℝ) := fun k => (sigma k)⁻¹ • ofLp (T (b (idx k))) with huvec
  refine ⟨r, ?_, trivial⟩
  refine
    { sigma := sigma
      u := uvec
      v := vvec
      sigma_pos := ?_
      u_orthonormal := ?_
      v_orthonormal := ?_
      decomp := ?_ }
  · -- sigma_pos
    intro k; exact hidx_pos k
  · -- u_orthonormal
    intro k l
    -- ∑_i u k i * u l i = (σk)⁻¹ (σl)⁻¹ * inner (T (b idx k)) (T (b idx l))
    have hinner : (inner ℝ (T (b (idx k))) (T (b (idx l))) : ℝ)
        = ∑ i, (ofLp (T (b (idx k)))) i * (ofLp (T (b (idx l)))) i := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl; intro i _
      rw [show (inner ℝ ((ofLp (T (b (idx k)))) i) ((ofLp (T (b (idx l)))) i) : ℝ)
            = (ofLp (T (b (idx l)))) i * (ofLp (T (b (idx k)))) i from rfl]
      ring
    have hsum : (∑ i, uvec k i * uvec l i)
        = (sigma k)⁻¹ * (sigma l)⁻¹ * inner ℝ (T (b (idx k))) (T (b (idx l))) := by
      rw [hinner, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      simp only [huvec, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsum, inner_Tv_eig T hn (idx k) (idx l)]
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl, if_pos rfl]
      have hsq : evals T hn (idx k) = sigma k ^ 2 := by
        rw [hsigma]; exact (sval_sq T hn (idx k)).symm
      rw [hsq]
      have hne : sigma k ≠ 0 := ne_of_gt (hidx_pos k)
      field_simp
    · have hne : idx k ≠ idx l := fun h => hkl (hidx_inj h)
      rw [if_neg hne, if_neg hkl]
      ring
  · -- v_orthonormal
    intro k l
    have hinner : (inner ℝ (b (idx k)) (b (idx l)) : ℝ)
        = ∑ j, vvec k j * vvec l j := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl; intro j _
      rw [show (inner ℝ ((ofLp (b (idx k))) j) ((ofLp (b (idx l))) j) : ℝ)
            = (ofLp (b (idx l))) j * (ofLp (b (idx k))) j from rfl]
      simp only [hvvec]; ring
    rw [← hinner, orthonormal_iff_ite.mp b.orthonormal (idx k) (idx l)]
    by_cases hkl : k = l
    · subst hkl; simp
    · have hne : idx k ≠ idx l := fun h => hkl (hidx_inj h)
      rw [if_neg hne, if_neg hkl]
  · -- decomp
    -- First: σ_k • u_k = ofLp (T (b (idx k))) as a Fin n1 → ℝ vector.
    have hsig_u : ∀ k, sigma k • uvec k = ofLp (T (b (idx k))) := by
      intro k
      funext i
      simp only [huvec, Pi.smul_apply, smul_eq_mul]
      have hne : sigma k ≠ 0 := ne_of_gt (hidx_pos k)
      field_simp
    -- Entry of the column N via T applied to basisFun.
    have hNij : ∀ (i : Fin n1) (j : Fin n2),
        N i j = (ofLp (T (EuclideanSpace.basisFun (Fin n2) ℝ j))) i := by
      intro i j
      rw [EuclideanSpace.basisFun_apply]
      rw [hT, Matrix.ofLp_toEuclideanLin_apply]
      simp only [Matrix.mulVec, EuclideanSpace.ofLp_single, dotProduct_single, mul_one]
    -- inner ⟨b k, basisFun j⟩ = (ofLp (b k)) j
    have hinner_bj : ∀ (k : Fin n2) (j : Fin n2),
        (inner ℝ (b k) (EuclideanSpace.basisFun (Fin n2) ℝ j) : ℝ) = (ofLp (b k)) j := by
      intro k j
      rw [PiLp.inner_apply, EuclideanSpace.basisFun_apply]
      rw [show (∑ x, (inner ℝ ((ofLp (b k)) x) ((ofLp (EuclideanSpace.single j (1:ℝ))) x) : ℝ))
            = ∑ x, (ofLp (EuclideanSpace.single j (1:ℝ))) x * (ofLp (b k)) x from
          Finset.sum_congr rfl (fun x _ => rfl)]
      simp only [EuclideanSpace.ofLp_single]
      rw [Finset.sum_eq_single j]
      · simp
      · intro x _ hx; simp [Pi.single_apply, hx]
      · intro h; exact absurd (Finset.mem_univ j) h
    -- The full-domain reconstruction at coordinate i:
    -- (ofLp (T (basisFun j))) i = ∑_{k : Fin n2} (ofLp (b k)) j * (ofLp (T (b k))) i
    have hrecon_coord : ∀ (i : Fin n1) (j : Fin n2),
        (ofLp (T (EuclideanSpace.basisFun (Fin n2) ℝ j))) i
          = ∑ k : Fin n2, (ofLp (b k)) j * (ofLp (T (b k))) i := by
      intro i j
      have hr := recon T hn (EuclideanSpace.basisFun (Fin n2) ℝ j)
      -- hr : T (basisFun j) = ∑ k, ⟨b k, basisFun j⟩ • T (b k)
      have := congrArg (fun (y : EuclideanSpace ℝ (Fin n1)) => (ofLp y) i) hr
      simp only at this
      rw [this]
      rw [WithLp.ofLp_sum, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [WithLp.ofLp_smul]
      simp only [Pi.smul_apply, smul_eq_mul, hb]
      rw [hinner_bj k j]
    -- Drop the zero terms (k ∉ P) and re-index by idx.
    have hsum_reindex : ∀ (i : Fin n1) (j : Fin n2),
        (∑ k : Fin n2, (ofLp (b k)) j * (ofLp (T (b k))) i)
          = ∑ k : Fin r, (ofLp (b (idx k))) j * (ofLp (T (b (idx k))) i) := by
      intro i j
      -- the full sum equals the sum over P (zero off P), then reindex P by e
      rw [← Finset.sum_subset (Finset.subset_univ P)
          (fun k _ hkP => ?_)]
      · -- ∑_{k ∈ P} f k = ∑_{x : Fin r} f (idx x) via the bijection idx
        symm
        apply Finset.sum_bij (fun (k : Fin r) (_ : k ∈ Finset.univ) => idx k)
        · intro k _; exact hidx_mem k
        · intro a _ c _ h; exact hidx_inj h
        · intro x hx
          refine ⟨(e.symm ⟨x, hx⟩), Finset.mem_univ _, ?_⟩
          simp only [hidx, Equiv.apply_symm_apply]
        · intro k _; rfl
      · -- term vanishes for k ∉ P (σ_k = 0)
        have hsv0 : sval T hn k = 0 := by
          rw [hP, Finset.mem_filter] at hkP
          push_neg at hkP
          have := hkP (Finset.mem_univ k)
          have hnn := sval_nonneg T hn k
          linarith
        have hTbk : T (b k) = 0 := by
          rw [hb]; exact Tv_zero_of_sval_zero T hn k hsv0
        rw [hTbk]
        simp
    -- Now assemble the matrix equality entrywise.
    funext i j
    simp only [hT] at hNij
    rw [hNij i j, hrecon_coord i j, hsum_reindex i j]
    -- RHS: (∑ k, σ_k • vecMulVec (u_k) (v_k)) i j
    rw [Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    -- σ_k * (u_k i * v_k j) = (ofLp (T (b idx k))) i * (ofLp (b idx k)) j
    have hu : sigma k * uvec k i = (ofLp (T (b (idx k)))) i := by
      have := congrArg (fun (w : Fin n1 → ℝ) => w i) (hsig_u k)
      simpa using this
    rw [show sigma k * (uvec k i * vvec k j) = (sigma k * uvec k i) * vvec k j by ring, hu]
    simp only [hvvec]
    ring


end MatrixCompletion

open MatrixCompletion
theorem solution {n1 n2 : Nat} (N : Matrix (Fin n1) (Fin n2) ℝ) :
    ∃ (r : Nat) (S : SVD N r), True :=
  MatrixCompletion._svd_exists_aux N
