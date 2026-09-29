-- Prove2me | solution 1 for mme_block_per_s_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-06-05T01:57:54.111242+00:00
-- url     : https://prove2.me/submissions/022f2ab1-ba1e-46d0-8a09-12a18962b8b6

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_block_tensor
import Definitions.Def_mme_laser_pattern
import Definitions.Def_mme_tensor
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_mmobj_mul
import Theorems.Thm_mme_block_per_s_factorization

/-! # `Sol_mme_block_per_s_factorization` — paper-agnostic per-s Kron composition.

Proof of `mme_block_per_s_factorization` by induction on `N`:

* **Base case (`N = 0`).** `T.kronPow 0 = oneObj` and the three empty products
  are `1`, so the goal becomes `Restrict (MMObj K 1 1 1) oneObj` — supplied
  by the explicit per-mode `K ← (Fin 1 × Fin 1 → K)` projection.

* **Inductive step (`N = N' + 1`).** Split the products via
  `Fin.prod_univ_succ`. Use the per-s witness at `τ 0` to get
  `Restrict (MMObj K (a (τ 0)) ...) (G.blockSubtensor s_fn)`; compose with the
  block→T restriction (blockProj is the witness) for
  `Restrict (MMObj K (a (τ 0)) ...) T`. Combine with the IH at the tail
  `τ' k = τ k.succ` via `kron_restrict_mono`, then transit through the
  multiplicativity isomorphism `MMObj_kron_iso`. -/

set_option maxHeartbeats 800000

open MME PiTensorProduct TensorProduct BigOperators

universe u

namespace MMEBlockPerSFactorization

variable {K : Type u} [Field K]

/-! ## Local helpers -/

/-- `interchange` on pure tensors gives a pure tensor of tensor products. -/
private theorem interchange_tprod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) = tprod K (fun i => v i ⊗ₜ[K] w i) := by
  dsimp [interchange]
  rw [PiTensorProduct.lift.tprod]
  dsimp [interchangeOuter]
  rw [PiTensorProduct.lift.tprod]
  rfl

/-- Naturality of the interchange map:
`map (fun i => f i ⊗ g i) (interchange t₁ t₂) = interchange (map f t₁) (map g t₂)`. -/
private theorem map_interchange {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V₁ V₂ V₃ V₄ : ι → Type u}
    [∀ i, AddCommGroup (V₁ i)] [∀ i, Module K (V₁ i)]
    [∀ i, AddCommGroup (V₂ i)] [∀ i, Module K (V₂ i)]
    [∀ i, AddCommGroup (V₃ i)] [∀ i, Module K (V₃ i)]
    [∀ i, AddCommGroup (V₄ i)] [∀ i, Module K (V₄ i)]
    (f : ∀ i, V₁ i →ₗ[K] V₃ i) (g : ∀ i, V₂ i →ₗ[K] V₄ i)
    (t₁ : PiTensorProduct K V₁) (t₂ : PiTensorProduct K V₂) :
    PiTensorProduct.map (fun i => TensorProduct.map (f i) (g i)) (interchange t₁ t₂) =
    interchange (PiTensorProduct.map f t₁) (PiTensorProduct.map g t₂) := by
  induction t₁ using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    induction t₂ using PiTensorProduct.induction_on with
    | smul_tprod c' v' =>
      simp only [map_smul, LinearMap.smul_apply]
      rw [interchange_tprod, PiTensorProduct.map_tprod, PiTensorProduct.map_tprod,
        PiTensorProduct.map_tprod, interchange_tprod]
      simp only [TensorProduct.map_tmul]
    | add x y ih1 ih2 =>
      simp only [map_add] at ih1 ih2 ⊢
      rw [ih1, ih2]
  | add x y ih1 ih2 =>
    simp only [map_add, LinearMap.add_apply, ih1, ih2]

/-- Kron monotonicity of `Restrict`: a Restrict on each factor lifts to the
Kronecker product. -/
private theorem kron_restrict_mono {d : ℕ} {X X' Y Y' : TensorObj K d}
    (hX : TensorObj.Restrict X X') (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  obtain ⟨f, hf⟩ := hX
  obtain ⟨g, hg⟩ := hY
  refine ⟨fun i => TensorProduct.map (f i) (g i), ?_⟩
  show PiTensorProduct.map (fun i => TensorProduct.map (f i) (g i))
      (interchange X'.t Y'.t) = interchange X.t Y.t
  rw [map_interchange, hf, hg]

/-- `Restrict (MMObj K 1 1 1) oneObj`: the explicit per-mode `K ← (Fin 1 × Fin 1 → K)`
projection. (Same construction as in `Def_mme_omega_normalize:263-300`.) -/
private theorem oneObj_restrict_MMObj_111 :
    TensorObj.Restrict (MMObj K 1 1 1) (TensorObj.oneObj : TensorObj K 3) := by
  -- the per-mode linear maps K → (Fin 1 × Fin 1 → K) sending c to Pi.single (0, 0) c
  let toMM : ∀ s : Fin 3, (TensorObj.oneObj : TensorObj K 3).V s →ₗ[K] (MMObj K 1 1 1).V s :=
    fun s => Fin.cases (LinearMap.smulRight (1 : K →ₗ[K] K) (Pi.single (0, 0) 1))
      (fun s => Fin.cases (LinearMap.smulRight (1 : K →ₗ[K] K) (Pi.single (0, 0) 1))
        (fun s => Fin.cases (LinearMap.smulRight (1 : K →ₗ[K] K) (Pi.single (0, 0) 1))
          (fun s => absurd s.isLt (by omega)) s) s) s
  refine ⟨toMM, ?_⟩
  -- Goal: PiTensorProduct.map toMM (tprod K (fun _ => (1 : K))) = (MMObj K 1 1 1).t
  show PiTensorProduct.map toMM (tprod K (fun _ : Fin 3 => (1 : K))) = (MMObj K 1 1 1).t
  -- Unfold (MMObj K 1 1 1).t as the single pure tensor.
  have hMM : (MMObj K 1 1 1).t =
      tprod K (fun s : Fin 3 =>
        match s with
        | ⟨0, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨1, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
        | ⟨2, _⟩ => (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)) := by
    show MMTensor K 1 1 1 = _
    unfold MMTensor
    rw [Fin.sum_univ_one, Fin.sum_univ_one, Fin.sum_univ_one]
    rfl
  rw [hMM]
  erw [PiTensorProduct.map_tprod]
  congr 1
  funext s
  fin_cases s <;>
    · change LinearMap.smulRight (1 : K →ₗ[K] K)
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) (1 : K) =
        (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K)
      simp [LinearMap.smulRight_apply]

/-- `Restrict (G.blockSubtensor σ) T`: the per-mode block projections are the
witness, and by definition of `blockTensor` they push `T.t` onto the σ-block. -/
private theorem blockSubtensor_restrict_T
    {d t : ℕ} {T : TensorObj K d} (G : T.TypeGrading t)
    (σ : Fin d → Fin t) :
    TensorObj.Restrict (G.blockSubtensor σ) T := by
  refine ⟨fun i => G.blockProj i (σ i), ?_⟩
  -- (G.blockSubtensor σ).t = G.blockTensor σ = PiTensorProduct.map blockProj T.t.
  rfl

/-- `Restrict (MMObj K (n*n') (m*m') (p*p')) (kron (MMObj K n m p) (MMObj K n' m' p'))`:
the .2 direction of `MMObj_kron_iso`. -/
private theorem MMObj_restrict_kron (n m p n' m' p' : ℕ) :
    TensorObj.Restrict
      (MMObj K (n * n') (m * m') (p * p'))
      (TensorObj.kron (MMObj K n m p) (MMObj K n' m' p')) :=
  (MMObj_kron_iso (K := K) n m p n' m' p').2

end MMEBlockPerSFactorization

open MMEBlockPerSFactorization

/-- **Paper-agnostic per-s Kron composition.** Closes
`Theorems/Thm_mme_block_per_s_factorization`. -/
theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} {t : ℕ}
    (G : T.TypeGrading t) (S : Finset (Fin t × Fin t × Fin t))
    (a b c : (Fin t × Fin t × Fin t) → ℕ)
    (_h_per_s_MM : ∀ s ∈ S,
        TensorObj.Restrict (MMObj K (a s) (b s) (c s))
          (G.blockSubtensor (fun i : Fin 3 =>
            match i with
            | ⟨0, _⟩ => s.1
            | ⟨1, _⟩ => s.2.1
            | ⟨2, _⟩ => s.2.2)))
    (N : ℕ)
    (τ : Fin N → Fin t × Fin t × Fin t)
    (_hτ_in_S : ∀ k : Fin N, τ k ∈ S) :
    TensorObj.Restrict
      (MMObj K
        (∏ k : Fin N, a (τ k))
        (∏ k : Fin N, b (τ k))
        (∏ k : Fin N, c (τ k)))
      (T.kronPow N) := by
  induction N with
  | zero =>
    -- ∏ k : Fin 0, ... = 1, and T.kronPow 0 = oneObj.
    -- Goal: Restrict (MMObj K 1 1 1) oneObj.
    simp only [Finset.prod_empty, Finset.univ_eq_empty]
    show TensorObj.Restrict (MMObj K 1 1 1) (TensorObj.oneObj : TensorObj K 3)
    exact oneObj_restrict_MMObj_111
  | succ N' ih =>
    -- T.kronPow (N'+1) = kron T (T.kronPow N').
    -- Use Fin.prod_univ_succ to split each product as (τ 0)-factor × tail product.
    -- Apply IH to the tail.
    set τ' : Fin N' → Fin t × Fin t × Fin t := fun k => τ k.succ with hτ'_def
    have hτ'_in_S : ∀ k : Fin N', τ' k ∈ S := fun k => _hτ_in_S k.succ
    have ih' := ih τ' hτ'_in_S
    -- per-s MM Restrict at τ 0
    have h_per_s_at_0 :=
      _h_per_s_MM (τ 0) (_hτ_in_S 0)
    -- the σ at τ 0
    set σ0 : Fin 3 → Fin t := fun i : Fin 3 =>
      match i with
      | ⟨0, _⟩ => (τ 0).1
      | ⟨1, _⟩ => (τ 0).2.1
      | ⟨2, _⟩ => (τ 0).2.2 with hσ0_def
    -- block→T restriction
    have h_block_T : TensorObj.Restrict (G.blockSubtensor σ0) T :=
      blockSubtensor_restrict_T G σ0
    -- Restrict (MMObj K (a (τ 0)) ...) T via transitivity.
    have h_MM_T : TensorObj.Restrict
        (MMObj K (a (τ 0)) (b (τ 0)) (c (τ 0))) T :=
      TensorObj.Restrict.trans h_per_s_at_0 h_block_T
    -- Kron monotonicity: combine h_MM_T and ih'.
    have h_kron : TensorObj.Restrict
        (TensorObj.kron (MMObj K (a (τ 0)) (b (τ 0)) (c (τ 0)))
          (MMObj K (∏ k : Fin N', a (τ' k)) (∏ k : Fin N', b (τ' k))
            (∏ k : Fin N', c (τ' k))))
        (TensorObj.kron T (T.kronPow N')) :=
      kron_restrict_mono h_MM_T ih'
    -- MMObj_kron_iso: Restrict (MMObj K product) (kron MMObj MMObj).
    have h_iso : TensorObj.Restrict
        (MMObj K
          ((a (τ 0)) * (∏ k : Fin N', a (τ' k)))
          ((b (τ 0)) * (∏ k : Fin N', b (τ' k)))
          ((c (τ 0)) * (∏ k : Fin N', c (τ' k))))
        (TensorObj.kron (MMObj K (a (τ 0)) (b (τ 0)) (c (τ 0)))
          (MMObj K (∏ k : Fin N', a (τ' k)) (∏ k : Fin N', b (τ' k))
            (∏ k : Fin N', c (τ' k)))) :=
      MMObj_restrict_kron
        (a (τ 0)) (b (τ 0)) (c (τ 0))
        (∏ k : Fin N', a (τ' k)) (∏ k : Fin N', b (τ' k))
        (∏ k : Fin N', c (τ' k))
    -- Combine: Restrict (MMObj product) (kron T (kronPow T N')).
    have h_combined :=
      TensorObj.Restrict.trans h_iso h_kron
    -- Goal: Restrict (MMObj (∏ a) (∏ b) (∏ c)) (kron T (kronPow T N')).
    -- The products ∏ k : Fin (N'+1), f (τ k) = f (τ 0) * ∏ k : Fin N', f (τ k.succ).
    have hprod_a :
        (∏ k : Fin (N' + 1), a (τ k)) =
          (a (τ 0)) * (∏ k : Fin N', a (τ' k)) := by
      rw [Fin.prod_univ_succ]
    have hprod_b :
        (∏ k : Fin (N' + 1), b (τ k)) =
          (b (τ 0)) * (∏ k : Fin N', b (τ' k)) := by
      rw [Fin.prod_univ_succ]
    have hprod_c :
        (∏ k : Fin (N' + 1), c (τ k)) =
          (c (τ 0)) * (∏ k : Fin N', c (τ' k)) := by
      rw [Fin.prod_univ_succ]
    rw [hprod_a, hprod_b, hprod_c]
    show TensorObj.Restrict
      (MMObj K
        ((a (τ 0)) * (∏ k : Fin N', a (τ' k)))
        ((b (τ 0)) * (∏ k : Fin N', b (τ' k)))
        ((c (τ 0)) * (∏ k : Fin N', c (τ' k))))
      (TensorObj.kronPow T (N' + 1))
    show TensorObj.Restrict
      (MMObj K
        ((a (τ 0)) * (∏ k : Fin N', a (τ' k)))
        ((b (τ 0)) * (∏ k : Fin N', b (τ' k)))
        ((c (τ 0)) * (∏ k : Fin N', c (τ' k))))
      (TensorObj.kron T (T.kronPow N'))
    exact h_combined
