-- Prove2me | solution 1 for mme_canonical_square_piece_restricts_restrictedPower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T09:47:21.949833+00:00
-- url     : https://prove2.me/submissions/0706ddb1-b70e-4ab7-b5b5-f169af8c083d

import Definitions.Def_mme_complete_split_canonical_square_data
import Definitions.Def_mme_recursive_yz_CW_cells
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_kron_pow_mode_word_basis
import Definitions.Def_mme_kron_pow_word_reindex
import Theorems.Thm_mme_kronPow_fiber_grouping_preserves_tensor_and_basis
import Theorems.Thm_mme_kronFin_family_mode_map_selected_basis
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes

universe u

set_option autoImplicit false

section part0

open MME MME.TensorObj MME.CompleteSplit MME.DWZComponentRestriction MME.DWZStep1Support Module
open PiTensorProduct TensorProduct BigOperators


set_option maxHeartbeats 400000

namespace D2P

variable {K : Type u} [Field K]

theorem basis_mpr_coe {ι : Type*} {V : Type*} [AddCommGroup V] [Module K V] {S T : Submodule K V}
    (h : S = T) (e : Basis ι K T = Basis ι K S) (B : Basis ι K S) (x : ι) :
    ((Eq.mpr e B : Basis ι K T) x : V) = (B x : V) := by
  subst h
  rfl

theorem coarseClassBasis_coe (q : ℕ) (i : Fin 3) (c : Fin 5) (p : CoarsePair q c) :
    ((coarseClassBasis (K := K) q i c p : (cwSquareCanonicalGrading K q).classOf i c) :
        (TensorObj.kron (CWObj K q) (CWObj K q)).V i) =
      cwSquareCanonicalBasis K q i p.1 := by
  have hS : Submodule.span K (Set.range fun p : CoarsePair q c ↦ cwSquareCanonicalBasis K q i p.1) =
      Submodule.span K (cwSquareCanonicalBasis K q i '' {p | cwSquarePairGrade q p = c}) := by
    congr 1
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  unfold coarseClassBasis
  simp only [id]
  exact (basis_mpr_coe hS _ _ p).trans (Basis.span_apply _ p)

theorem interchange_pure
    {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) =
      tprod K (fun i ↦ v i ⊗ₜ[K] w i) := by
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  change (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

theorem map_interchange
    {V₁ V₂ V₃ V₄ : Fin 3 → Type u}
    [∀ i, AddCommGroup (V₁ i)] [∀ i, Module K (V₁ i)]
    [∀ i, AddCommGroup (V₂ i)] [∀ i, Module K (V₂ i)]
    [∀ i, AddCommGroup (V₃ i)] [∀ i, Module K (V₃ i)]
    [∀ i, AddCommGroup (V₄ i)] [∀ i, Module K (V₄ i)]
    (f : ∀ i, V₁ i →ₗ[K] V₃ i) (g : ∀ i, V₂ i →ₗ[K] V₄ i)
    (a : PiTensorProduct K V₁) (b : PiTensorProduct K V₂) :
    PiTensorProduct.map (fun i ↦ TensorProduct.map (f i) (g i)) (interchange a b) =
      interchange (PiTensorProduct.map f a) (PiTensorProduct.map g b) := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    induction b using PiTensorProduct.induction_on with
    | smul_tprod c' w =>
      simp only [map_smul, LinearMap.smul_apply]
      rw [interchange_pure, PiTensorProduct.map_tprod, PiTensorProduct.map_tprod,
        PiTensorProduct.map_tprod, interchange_pure]
      simp only [TensorProduct.map_tmul]
    | add x y ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
  | add x y ih₁ ih₂ => simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

/-- Dropping the trailing unit factor of a tensor power. -/
theorem map_rid
    {V : Fin 3 → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (a : PiTensorProduct K V) :
    PiTensorProduct.map (fun i ↦ (TensorProduct.rid K (V i)).toLinearMap)
      (interchange a (tprod K (fun _ ↦ (1 : K)))) = a := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    simp only [map_smul, LinearMap.smul_apply]
    rw [interchange_pure, PiTensorProduct.map_tprod]
    simp only [LinearEquiv.coe_coe, TensorProduct.rid_tmul, one_smul]
  | add x y ih₁ ih₂ => simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

/-- Drop the trailing unit factor of `T ⊗ (T ⊗ K)`. -/
noncomputable def pairDrop (T : TensorObj K 3) (i : Fin 3) :
    (T.kronPow 2).V i →ₗ[K] (TensorObj.kron T T).V i :=
  TensorProduct.map (LinearMap.id : T.V i →ₗ[K] T.V i) (TensorProduct.rid K (T.V i)).toLinearMap

/-- `T^{⊗2} = T ⊗ (T ⊗ 1)`; dropping the unit gives `T ⊗ T`, for any tensor. -/
theorem pair_map_tensor (T : TensorObj K 3) :
    PiTensorProduct.map (pairDrop T) (T.kronPow 2).t = (TensorObj.kron T T).t := by
  have h2 : (T.kronPow 2).t = interchange T.t (interchange T.t (tprod K fun _ ↦ (1 : K))) := rfl
  rw [h2]
  unfold pairDrop
  erw [map_interchange, PiTensorProduct.map_id, LinearMap.id_apply (R := K), map_rid]
  rfl

/-- One more letter at the front of a word basis vector. -/
theorem word_succ (T : TensorObj K 3) (i : Fin 3) {ι : Type u} (b : Basis ι K (T.V i)) (n : ℕ)
    (v : Fin (n + 1) → ι) :
    kronPowModeWordBasis T i b (n + 1) v =
      (b (v 0) ⊗ₜ[K] kronPowModeWordBasis T i b n (Fin.tail v) : T.V i ⊗[K] (T.kronPow n).V i) := by
  rw [kronPowModeWordBasis]
  erw [Basis.reindex_apply, Basis.tensorProduct_apply]

theorem pair_map_word (T : TensorObj K 3) (i : Fin 3) {ι : Type u} (b : Basis ι K (T.V i))
    (v : Fin 2 → ι) :
    pairDrop T i (kronPowModeWordBasis T i b 2 v) = b (v 0) ⊗ₜ[K] b (v 1) := by
  unfold pairDrop
  erw [word_succ, TensorProduct.map_tmul, LinearMap.id_apply, word_succ, LinearEquiv.coe_coe,
    TensorProduct.rid_tmul]
  rw [kronPowModeWordBasis]
  erw [Basis.singleton_apply, one_smul]
  rfl

/-- The canonical CW basis, lifted in universe, used by `CWCells.basis`. -/
noncomputable abbrev cwb (i : Fin 3) : Basis (ULift.{u} (Fin (5 + 2))) K ((CWObj K 5).V i) :=
  (cwThreeCanonicalBasis K 5 i).reindex Equiv.ulift.symm

theorem cwb_tmul (i : Fin 3) (a b : ULift.{u} (Fin (5 + 2))) :
    cwb (K := K) i a ⊗ₜ[K] cwb (K := K) i b = cwSquareCanonicalBasis K 5 i (a.down, b.down) := by
  unfold cwb
  rw [Basis.reindex_apply, Basis.reindex_apply]
  fin_cases i <;> exact (Basis.tensorProduct_apply _ _ _ _).symm

theorem sq_mem (i : Fin 3) (p : Fin (5 + 2) × Fin (5 + 2)) :
    cwSquareCanonicalBasis K 5 i p ∈
      (cwSquareCanonicalGrading K 5).classOf i (cwSquarePairGrade 5 p) :=
  Submodule.subset_span ⟨p, rfl, rfl⟩

theorem sqBasis_coe (ρ : Fin 3 → Fin 5) (i : Fin 3) (x : CoarsePair 5 (ρ i)) :
    (show ↥((cwSquareCanonicalGrading K 5).classOf i (ρ i)) from
        CompleteSplitCanonicalSquare.basis K 5 ρ i ⟨x⟩).val = cwSquareCanonicalBasis K 5 i x.1 := by
  unfold CompleteSplitCanonicalSquare.basis
  exact (congrArg Subtype.val (Basis.reindex_apply _ _ _)).trans (coarseClassBasis_coe 5 i (ρ i) x)

/-- The per-factor map `CW ⊗ CW ⊗ 1 → block ρ`. -/
noncomputable def factorMap (ρ : Fin 3 → Fin 5) (i : Fin 3) :
    ((CWObj K 5).kronPow 2).V i →ₗ[K] (CompleteSplitCanonicalSquare.obj K 5 ρ).V i :=
  ((cwSquareCanonicalGrading K 5).blockProj i (ρ i)).comp (pairDrop (CWObj K 5) i)

/-- Drop-then-project carries `T^{⊗2}` to any block of any grading of `T ⊗ T` (generic, so no
concrete tensor is ever unfolded). -/
theorem blockDrop_tensor (T : TensorObj K 3) {t : ℕ} (G : (TensorObj.kron T T).TypeGrading t)
    (σ : Fin 3 → Fin t) :
    PiTensorProduct.map (fun i ↦ (G.blockProj i (σ i)).comp (pairDrop T i)) (T.kronPow 2).t =
      (G.blockSubtensor σ).t := by
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply, pair_map_tensor]
  rfl

theorem factorMap_tensor (ρ : Fin 3 → Fin 5) :
    PiTensorProduct.map (factorMap (K := K) ρ) ((CWObj K 5).kronPow 2).t =
      (CompleteSplitCanonicalSquare.obj K 5 ρ).t :=
  blockDrop_tensor (CWObj K 5) (cwSquareCanonicalGrading K 5) ρ

theorem factorMap_pair (ρ : Fin 3 → Fin 5) (i : Fin 3) (v : Fin 2 → ULift.{u} (Fin (5 + 2))) :
    factorMap (K := K) ρ i (kronPowModeWordBasis (CWObj K 5) i (cwb (K := K) i) 2 v) =
      (cwSquareCanonicalGrading K 5).blockProj i (ρ i)
        (cwSquareCanonicalBasis K 5 i ((v 0).down, (v 1).down)) := by
  show (cwSquareCanonicalGrading K 5).blockProj i (ρ i)
      (pairDrop (CWObj K 5) i (kronPowModeWordBasis (CWObj K 5) i (cwb (K := K) i) 2 v)) = _
  rw [pair_map_word, cwb_tmul]

theorem factorMap_in (ρ : Fin 3 → Fin 5) (i : Fin 3) (v : Fin 2 → ULift.{u} (Fin (5 + 2)))
    (h : cwSquarePairGrade 5 ((v 0).down, (v 1).down) = ρ i) :
    factorMap (K := K) ρ i (kronPowModeWordBasis (CWObj K 5) i (cwb (K := K) i) 2 v) =
      CompleteSplitCanonicalSquare.basis K 5 ρ i ⟨⟨((v 0).down, (v 1).down), h⟩⟩ := by
  rw [factorMap_pair]
  have hm : cwSquareCanonicalBasis K 5 i ((v 0).down, (v 1).down) ∈
      (cwSquareCanonicalGrading K 5).classOf i (ρ i) := by
    rw [← h]; exact sq_mem i _
  rw [TensorObj.TypeGrading.blockProj_apply_mem _ i (ρ i) _ hm]
  apply Subtype.ext
  exact (sqBasis_coe ρ i ⟨_, h⟩).symm

theorem factorMap_out (ρ : Fin 3 → Fin 5) (i : Fin 3) (v : Fin 2 → ULift.{u} (Fin (5 + 2)))
    (h : cwSquarePairGrade 5 ((v 0).down, (v 1).down) ≠ ρ i) :
    factorMap (K := K) ρ i (kronPowModeWordBasis (CWObj K 5) i (cwb (K := K) i) 2 v) = 0 := by
  rw [factorMap_pair]
  exact TensorObj.TypeGrading.blockProj_apply_mem_ne _ i (ρ i) _ (Ne.symm h) _ (sq_mem i _)

end D2P

end part0

section part1

open MME MME.TensorObj MME.CompleteSplit MME.DWZComponentRestriction Module
open PiTensorProduct TensorProduct BigOperators


set_option maxHeartbeats 400000

namespace D2P

variable {K : Type u} [Field K]

/-- One more factor at the front of a `kronFin` product basis vector. -/
theorem pi_succ {d n : ℕ} (X : Fin (n + 1) → TensorObj K d) (i : Fin d)
    {index : Fin (n + 1) → Type u} (b : ∀ j, Basis (index j) K ((X j).V i)) (w : ∀ j, index j) :
    kronFinModePiBasis (n + 1) X i b w =
      ((b 0 (w 0)) ⊗ₜ[K] kronFinModePiBasis n (fun j ↦ X j.succ) i (fun j ↦ b j.succ)
        (fun j ↦ w j.succ) : (X 0).V i ⊗[K] (TensorObj.kronFin n (fun j ↦ X j.succ)).V i) := by
  rw [kronFinModePiBasis]
  erw [Basis.reindex_apply, Basis.tensorProduct_apply]
  rfl

/-- A factor that sends its basis vector to `0` kills the whole product basis vector. -/
theorem family_map_zero {d : ℕ} : ∀ (n : ℕ) (X Y : Fin n → TensorObj K d)
    (f : ∀ r i, (X r).V i →ₗ[K] (Y r).V i) (i : Fin d) {index : Fin n → Type u}
    (b : ∀ r, Basis (index r) K ((X r).V i)) (w : ∀ r, index r) (r0 : Fin n),
    f r0 i (b r0 (w r0)) = 0 →
    kronFinFamilyModeMap n X Y f i (kronFinModePiBasis n X i b w) = 0
  | 0, _, _, _, _, _, _, _, r0, _ => r0.elim0
  | n + 1, X, Y, f, i, index, b, w, r0, h0 => by
    rw [pi_succ]
    change TensorProduct.map (f 0 i)
      (kronFinFamilyModeMap n (fun r : Fin n ↦ X r.succ) (fun r : Fin n ↦ Y r.succ)
        (fun r j ↦ f r.succ j) i) _ = 0
    rw [TensorProduct.map_tmul]
    refine Fin.cases (motive := fun r0 ↦ f r0 i (b r0 (w r0)) = 0 → _) ?_ ?_ r0 h0
    · intro h; rw [h, zero_tmul]
    · intro r1 h
      rw [family_map_zero n (fun r : Fin n ↦ X r.succ) (fun r : Fin n ↦ Y r.succ)
        (fun r j ↦ f r.succ j) i (fun r ↦ b r.succ) (fun r ↦ w r.succ) r1 h, tmul_zero]

/-- `⊗_{j<N} Y → Y^{⊗N}`, factor by factor. -/
noncomputable def toPow (Y : TensorObj K 3) (i : Fin 3) :
    (N : ℕ) → (TensorObj.kronFin N (fun _ ↦ Y)).V i →ₗ[K] (Y.kronPow N).V i
  | 0 => LinearMap.id
  | N + 1 => TensorProduct.map (LinearMap.id : Y.V i →ₗ[K] Y.V i) (toPow Y i N)

theorem toPow_tensor (Y : TensorObj K 3) :
    ∀ N : ℕ, PiTensorProduct.map (fun i ↦ toPow Y i N) (TensorObj.kronFin N (fun _ ↦ Y)).t =
      (Y.kronPow N).t
  | 0 => by
    change PiTensorProduct.map (fun _ ↦ LinearMap.id) _ = _
    rw [PiTensorProduct.map_id]
    rfl
  | N + 1 => by
    change PiTensorProduct.map (fun i ↦ TensorProduct.map (LinearMap.id : Y.V i →ₗ[K] Y.V i)
      (toPow Y i N)) (interchange Y.t (TensorObj.kronFin N (fun _ ↦ Y)).t) =
      interchange Y.t (Y.kronPow N).t
    rw [map_interchange, PiTensorProduct.map_id, LinearMap.id_apply, toPow_tensor Y N]

theorem pow_succ_basis (Y : TensorObj K 3) (i : Fin 3) {ι : Type u} (c : Basis ι K (Y.V i))
    (N : ℕ) (a : ι) (w : PowIndex ι N) :
    kronPowModeBasis Y i c (N + 1) (a, w) =
      (c a ⊗ₜ[K] kronPowModeBasis Y i c N w : Y.V i ⊗[K] (Y.kronPow N).V i) := by
  rw [kronPowModeBasis]
  erw [Basis.tensorProduct_apply]

theorem toPow_basis (Y : TensorObj K 3) (i : Fin 3) {ι : Type u} (c : Basis ι K (Y.V i)) :
    ∀ (N : ℕ) (w : Fin N → ι),
      toPow Y i N (kronFinModePiBasis N (fun _ ↦ Y) i (fun _ ↦ c) w) =
        kronPowModeBasis Y i c N (PowIndex.ofFun N w)
  | 0, w => by
    change (kronFinModePiBasis 0 (fun _ ↦ Y) i (fun _ ↦ c) w) =
      kronPowModeBasis Y i c 0 (PowIndex.ofFun 0 w)
    rw [kronFinModePiBasis, kronPowModeBasis]
    erw [Basis.singleton_apply, Basis.singleton_apply]
  | N + 1, w => by
    rw [pi_succ]
    change TensorProduct.map (LinearMap.id : Y.V i →ₗ[K] Y.V i) (toPow Y i N) _ = _
    rw [TensorProduct.map_tmul, LinearMap.id_apply, toPow_basis Y i c N]
    exact (pow_succ_basis Y i c N (w 0) _).symm

end D2P

end part1

section part2

open MME MME.TensorObj MME.CompleteSplit MME.DWZComponentRestriction Module
open PiTensorProduct TensorProduct BigOperators


set_option maxHeartbeats 400000

namespace D2P

variable {K : Type u} [Field K]

/-- Four restriction maps compose (generic, so nothing concrete unfolds). -/
theorem map_comp4 {V₁ V₂ V₃ V₄ V₅ : Fin 3 → Type u}
    [∀ i, AddCommGroup (V₁ i)] [∀ i, Module K (V₁ i)] [∀ i, AddCommGroup (V₂ i)]
    [∀ i, Module K (V₂ i)] [∀ i, AddCommGroup (V₃ i)] [∀ i, Module K (V₃ i)]
    [∀ i, AddCommGroup (V₄ i)] [∀ i, Module K (V₄ i)] [∀ i, AddCommGroup (V₅ i)]
    [∀ i, Module K (V₅ i)]
    (a : ∀ i, V₁ i →ₗ[K] V₂ i) (b : ∀ i, V₂ i →ₗ[K] V₃ i) (c : ∀ i, V₃ i →ₗ[K] V₄ i)
    (d : ∀ i, V₄ i →ₗ[K] V₅ i)
    (t₁ : PiTensorProduct K V₁) (t₂ : PiTensorProduct K V₂) (t₃ : PiTensorProduct K V₃)
    (t₄ : PiTensorProduct K V₄) (t₅ : PiTensorProduct K V₅)
    (ha : PiTensorProduct.map a t₁ = t₂) (hb : PiTensorProduct.map b t₂ = t₃)
    (hc : PiTensorProduct.map c t₃ = t₄) (hd : PiTensorProduct.map d t₄ = t₅) :
    PiTensorProduct.map (fun i ↦ (d i).comp ((c i).comp ((b i).comp (a i)))) t₁ = t₅ := by
  simp only [PiTensorProduct.map_comp, LinearMap.comp_apply, ha, hb, hc, hd]

/-- The pairing of the `2N` atomic slots into `N` squares, slot `2j + r` in square `j`. -/
def pairing (N : ℕ) : Fin (N * 2 ^ (2 - 1)) ≃ (Σ _ : Fin N, Fin 2) :=
  (finProdFinEquiv (m := N) (n := 2)).symm.trans (Equiv.sigmaEquivProd (Fin N) (Fin 2)).symm

theorem pairing_symm (N : ℕ) (j : Fin N) (r : Fin 2) :
    (pairing N).symm ⟨j, r⟩ = finProdFinEquiv (j, r) := rfl

/-- The square at position `j` of an atomic word. -/
def pairAt {N : ℕ} (x : Fin (N * 2 ^ (2 - 1)) → ULift.{u} (Fin (5 + 2))) (j : Fin N) :
    Fin (5 + 2) × Fin (5 + 2) :=
  ((x (finProdFinEquiv (j, 0))).down, (x (finProdFinEquiv (j, 1))).down)

/-- A basis vector outside the allowed set has zero allowed projection. -/
theorem disallowed_projection_zero (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i)) (allowed : (i : Fin 3) → ι i → Prop)
    (i : Fin 3) (j : ι i) (hj : ¬ allowed i j) :
    (T.basisAllAllowedGrading b allowed).blockProj i 0 (b i j) = 0 := by
  classical
  let G := T.basisAllAllowedGrading b allowed
  have hx : b i j ∈ G.classOf i 1 := by
    change b i j ∈ cwBasisGrade (b i) (fun k ↦ if allowed i k then (0 : Fin 2) else 1) 1
    exact Submodule.subset_span ⟨j, by simp only [Set.mem_setOf_eq, if_neg hj], rfl⟩
  exact (G.is_internal i).ofBijective_coeLinearMap_of_mem_ne (show (1 : Fin 2) ≠ 0 by decide) hx

/-- The fine-grade word of square `j` is its canonical square label. -/
theorem label_pair {N : ℕ} (ρ : Fin 3 → Fin 5) (i : Fin 3)
    (x : Fin (N * 2 ^ (2 - 1)) → ULift.{u} (Fin (5 + 2))) (j : Fin N)
    (h : cwSquarePairGrade 5 (pairAt x j) = ρ i) :
    CompleteSplitCanonicalSquare.label 5 ρ i ⟨⟨pairAt x j, h⟩⟩ =
      RecursiveYZ.CWCells.label 5 2 N (Equiv.refl _) x j := by
  funext r
  fin_cases r <;> rfl

/-- In-block squares with exactly the prescribed counts form an allowed word of the piece. -/
theorem allowed_of {N : ℕ} (ρ : Fin 3 → Fin 5) (beta : Fin 3 → CompleteSplit.Profile 2)
    (mu : Fin 3 → CompleteSplit.CompleteWord 2 → ℕ)
    (hmu : ∀ i σ, (mu i σ : ℝ) = N * (beta i).probability σ) (i : Fin 3)
    (x : Fin (N * 2 ^ (2 - 1)) → ULift.{u} (Fin (5 + 2)))
    (hin : ∀ j, cwSquarePairGrade 5 (pairAt x j) = ρ i)
    (hc : ApproxConsistent (CompleteSplitCanonicalSquare.label 5 ρ i) (beta i) 0
      (PowIndex.ofFun N (fun j ↦ (⟨⟨pairAt x j, hin j⟩⟩ : CompleteSplitCanonicalSquare.Coord 5 ρ i)))) :
    RecursiveYZ.CWCells.allowed 5 2 N (Equiv.refl _) (fun _ ↦ Unit.unit)
      (fun _ i ↦ (ρ i).val) (fun i _ ↦ mu i) i x := by
  classical
  refine ⟨fun p ↦ ?_, fun c σ ↦ ?_⟩
  · have hp := congrArg Fin.val (hin p)
    show ∑ r : Fin 2, (RecursiveYZ.CWCells.label 5 2 N (Equiv.refl _) x p r).val = (ρ i).val
    rw [Fin.sum_univ_two, ← hp]
    rfl
  · have hσ := hc σ
    simp only [NNReal.coe_zero, mul_zero, abs_nonpos_iff, sub_eq_zero] at hσ
    rw [← hmu i σ] at hσ
    have hcount : wordCount (CompleteSplitCanonicalSquare.label 5 ρ i)
        (PowIndex.ofFun N (fun j ↦ (⟨⟨pairAt x j, hin j⟩⟩ : CompleteSplitCanonicalSquare.Coord 5 ρ i)))
        σ = mu i σ := by exact_mod_cast hσ
    show RecursiveYZ.count (fun _ ↦ ()) (RecursiveYZ.CWCells.label 5 2 N (Equiv.refl (Fin N)) x) c σ =
      mu i σ
    rw [← hcount]
    unfold RecursiveYZ.count wordCount
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, PowIndex.get_ofFun]
    rw [label_pair ρ i x j (hin j)]

/-- **D2′.** A cell piece of `N` squares of coarse type `ρ` with exact child counts `μ` contains
the exact-profile power of the canonical square block `ρ`. -/
theorem piece_restricts_restrictedPower (ρ : Fin 3 → Fin 5) (N : ℕ)
    (beta : Fin 3 → CompleteSplit.Profile 2) (mu : Fin 3 → CompleteSplit.CompleteWord 2 → ℕ)
    (hmu : ∀ i σ, (mu i σ : ℝ) = N * (beta i).probability σ) :
    TensorObj.Restrict
      (CompleteSplit.restrictedPower (CompleteSplitCanonicalSquare.obj K 5 ρ)
        (CompleteSplitCanonicalSquare.basis K 5 ρ) (CompleteSplitCanonicalSquare.label 5 ρ) beta 0 N)
      (RecursiveYZ.CWCells.unbroken K 5 2 N (Equiv.refl _) (fun _ ↦ Unit.unit)
        (fun _ i ↦ (ρ i).val) (fun i _ ↦ mu i)) := by
  classical
  obtain ⟨Φ, hΦt, hΦb⟩ := mme_kronPow_fiber_grouping_preserves_tensor_and_basis (CWObj K 5)
    (fun i ↦ cwb (K := K) i) (fun _ : Fin N ↦ 2) (pairing N)
  let G := ((CompleteSplitCanonicalSquare.obj K 5 ρ).kronPow N).basisAllAllowedGrading
    (fun i ↦ kronPowModeBasis (CompleteSplitCanonicalSquare.obj K 5 ρ) i
      (CompleteSplitCanonicalSquare.basis K 5 ρ i) N)
    (fun i ↦ ApproxConsistent (CompleteSplitCanonicalSquare.label 5 ρ i) (beta i) 0)
  let F := fun i ↦ kronFinFamilyModeMap N (fun _ ↦ (CWObj K 5).kronPow 2)
    (fun _ ↦ CompleteSplitCanonicalSquare.obj K 5 ρ) (fun _ i ↦ factorMap (K := K) ρ i) i
  refine mme_restrict_basisAllAllowedSubtensor_of_vanishes
    (RecursiveYZ.CWCells.source K 5 2 N)
    (((CompleteSplitCanonicalSquare.obj K 5 ρ).kronPow N).basisAllAllowedSubtensor
      (fun i ↦ kronPowModeBasis (CompleteSplitCanonicalSquare.obj K 5 ρ) i
        (CompleteSplitCanonicalSquare.basis K 5 ρ i) N)
      (fun i ↦ ApproxConsistent (CompleteSplitCanonicalSquare.label 5 ρ i) (beta i) 0))
    (RecursiveYZ.CWCells.basis K 5 2 N)
    (RecursiveYZ.CWCells.allowed 5 2 N (Equiv.refl _) (fun _ ↦ Unit.unit)
      (fun _ i ↦ (ρ i).val) (fun i _ ↦ mu i))
    (fun i ↦ (G.blockProj i 0).comp ((toPow (CompleteSplitCanonicalSquare.obj K 5 ρ) i N).comp
      ((F i).comp (Φ i).toLinearMap))) ?_ ?_
  · exact map_comp4 (fun i ↦ (Φ i).toLinearMap) F
      (fun i ↦ toPow (CompleteSplitCanonicalSquare.obj K 5 ρ) i N) (fun i ↦ G.blockProj i 0)
      _ _ _ _ _ hΦt
      (kronFinFamilyModeMap_preserves_tensor _ _ _ (fun _ ↦ factorMap_tensor ρ))
      (toPow_tensor _ N) rfl
  · intro i x hx
    have hΦx := hΦb i x
    by_cases hin : ∀ j, cwSquarePairGrade 5 (pairAt x j) = ρ i
    · have hF : F i (Φ i (RecursiveYZ.CWCells.basis K 5 2 N i x)) =
          kronFinModePiBasis N (fun _ ↦ CompleteSplitCanonicalSquare.obj K 5 ρ) i
            (fun _ ↦ CompleteSplitCanonicalSquare.basis K 5 ρ i)
            (fun j ↦ (⟨⟨pairAt x j, hin j⟩⟩ : CompleteSplitCanonicalSquare.Coord 5 ρ i)) := by
        show F i (Φ i (kronPowModeWordBasis (CWObj K 5) i (cwb (K := K) i) (N * 2 ^ (2 - 1)) x)) = _
        rw [hΦx]
        exact mme_kronFin_family_mode_map_selected_basis _ _ i _ _ _ _ _
          (fun j ↦ factorMap_in ρ i _ (hin j))
      show G.blockProj i 0 (toPow (CompleteSplitCanonicalSquare.obj K 5 ρ) i N
        (F i (Φ i (RecursiveYZ.CWCells.basis K 5 2 N i x)))) = 0
      rw [hF, toPow_basis]
      apply disallowed_projection_zero
      exact fun hc ↦ hx (allowed_of ρ beta mu hmu i x hin hc)
    · push_neg at hin
      obtain ⟨j, hj⟩ := hin
      have hF : F i (Φ i (RecursiveYZ.CWCells.basis K 5 2 N i x)) = 0 := by
        show F i (Φ i (kronPowModeWordBasis (CWObj K 5) i (cwb (K := K) i) (N * 2 ^ (2 - 1)) x)) = _
        rw [hΦx]
        exact family_map_zero N _ _ _ i _ _ j (factorMap_out ρ i _ hj)
      show G.blockProj i 0 (toPow (CompleteSplitCanonicalSquare.obj K 5 ρ) i N
        (F i (Φ i (RecursiveYZ.CWCells.basis K 5 2 N i x)))) = 0
      rw [hF, map_zero, map_zero]

end D2P

end part2

open MME

theorem solution {K : Type u} [Field K]
    (ρ : Fin 3 → Fin 5) (N : ℕ) (beta : Fin 3 → CompleteSplit.Profile 2)
    (mu : Fin 3 → CompleteSplit.CompleteWord 2 → ℕ)
    (hmu : ∀ i σ, (mu i σ : ℝ) = N * (beta i).probability σ) :
    TensorObj.Restrict
      (CompleteSplit.restrictedPower (CompleteSplitCanonicalSquare.obj K 5 ρ)
        (CompleteSplitCanonicalSquare.basis K 5 ρ) (CompleteSplitCanonicalSquare.label 5 ρ) beta 0 N)
      (RecursiveYZ.CWCells.unbroken K 5 2 N (Equiv.refl _) (fun _ ↦ Unit.unit)
        (fun _ i ↦ (ρ i).val) (fun i _ ↦ mu i)) :=
  D2P.piece_restricts_restrictedPower ρ N beta mu hmu
