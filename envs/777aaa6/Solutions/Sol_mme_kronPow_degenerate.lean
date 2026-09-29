-- Prove2me | solution 1 for mme_kronPow_degenerate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-28T22:24:07.750742+00:00
-- url     : https://prove2.me/submissions/031a9f94-989a-44ca-abd2-3556a93cdf1d

import Definitions.Def_mme_degeneration
import Definitions.Def_mme_tensor_rank
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Solution: degeneration is multiplicative under Kronecker powers

If `X` degenerates from `I_r` of order `h`, then `X^⊗m` degenerates from `I_{r^m}` of
order `m·h`. Proof by induction on `m`, using:

* `degeneratesOfOrder_kron` — Kronecker of two degenerations adds orders;
* `restrict_diag_kron` — `I_{r₁} ⊗ I_{r₂}` restricts (order-0 degenerates) to `I_{r₁·r₂}`;
* `degeneratesOfOrder_of_restrict_right` — transport a degeneration along a restriction
  of the bigger (right) side.

All helper definitions/lemmas are `private` and inline. Adapted (not copied) from the
Prism `Degeneration.lean` development: Prism uses its `liftMap` wrapper and assumes
`[Fact (1 < d)]`; here we use `PiTensorProduct.map` directly with no `Fact` and a single
universe `u`. -/

open MME PiTensorProduct TensorProduct BigOperators

universe u

set_option maxHeartbeats 1000000

namespace MME

variable {K : Type u} [Field K] {d : ℕ}

/-! ## Helper lemmas about `PiTensorProduct.map` and `interchange` -/

/-- If a family of linear maps has a zero entry at some mode `i₀`, then
`PiTensorProduct.map` of that family is the zero map. -/
private theorem map_eq_zero_of_zero_slot {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    {g : ∀ i, V i →ₗ[K] W i} {i₀ : Fin d} (hg : g i₀ = 0) :
    PiTensorProduct.map g = (0 : PiTensorProduct K V →ₗ[K] PiTensorProduct K W) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext; intro v
  simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod,
    LinearMap.zero_apply]
  apply MultilinearMap.map_coord_zero (tprod K) (i := i₀)
  rw [hg]; rfl

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

/-- `PiTensorProduct.map` of a family of finite sums expands as a sum over the
product index set. -/
private theorem map_sum_piFinset {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    {α : Fin d → Type*} (S : ∀ i, Finset (α i))
    (g : ∀ i, α i → (V i →ₗ[K] W i)) :
    PiTensorProduct.map (fun i => ∑ j ∈ S i, g i j) =
      ∑ c ∈ Fintype.piFinset S, PiTensorProduct.map (fun i => g i (c i)) := by
  apply PiTensorProduct.ext; apply MultilinearMap.ext; intro v
  simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod,
    LinearMap.sum_apply]
  exact MultilinearMap.map_sum_finset (tprod K) (fun i j => g i j (v i)) S

/-- Reindexing of nested sums over antidiagonal tuples. Copied verbatim from Prism
(uses no tensor machinery). -/
private theorem sum_antidiagTuple_piFinset_antidiag {β : Type*} [AddCommMonoid β]
    {d k : ℕ} (F : (Fin d → ℕ) → (Fin d → ℕ) → β) :
    ∑ j ∈ Finset.Nat.antidiagonalTuple d k,
      ∑ c ∈ Fintype.piFinset (fun i => Finset.antidiagonal (j i)),
        F (fun i => (c i).1) (fun i => (c i).2) =
    ∑ p ∈ Finset.antidiagonal k,
      ∑ j₁ ∈ Finset.Nat.antidiagonalTuple d p.1,
        ∑ j₂ ∈ Finset.Nat.antidiagonalTuple d p.2,
          F j₁ j₂ := by
  rw [Finset.sum_sigma']
  conv_rhs => rw [Finset.sum_sigma']
  simp_rw [Finset.sum_sigma']
  apply Finset.sum_nbij'
    (fun ⟨j, c⟩ => ⟨⟨(∑ i, (c i).1, ∑ i, (c i).2), fun i => (c i).1⟩, fun i => (c i).2⟩)
    (fun ⟨⟨_, j₁⟩, j₂⟩ => ⟨fun i => j₁ i + j₂ i, fun i => (j₁ i, j₂ i)⟩)
  · rintro ⟨j, c⟩ hm
    rw [Finset.mem_sigma] at hm
    dsimp only at hm
    have hj := Finset.Nat.mem_antidiagonalTuple.mp hm.1
    have hc : ∀ i, (c i) ∈ Finset.antidiagonal (j i) :=
      Fintype.mem_piFinset.mp hm.2
    refine Finset.mem_sigma.mpr ⟨Finset.mem_sigma.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_antidiagonal.mpr (by
        rw [← Finset.sum_add_distrib, ← hj]
        exact Finset.sum_congr rfl fun i _ => Finset.mem_antidiagonal.mp (hc i))
    · exact Finset.Nat.mem_antidiagonalTuple.mpr rfl
    · exact Finset.Nat.mem_antidiagonalTuple.mpr rfl
  · rintro ⟨⟨p, j₁⟩, j₂⟩ hm
    rw [Finset.mem_sigma] at hm
    rw [Finset.mem_sigma] at hm
    dsimp only at hm
    have hp := Finset.mem_antidiagonal.mp hm.1.1
    have hj₁ := Finset.Nat.mem_antidiagonalTuple.mp hm.1.2
    have hj₂ := Finset.Nat.mem_antidiagonalTuple.mp hm.2
    refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
    · rw [Finset.Nat.mem_antidiagonalTuple]
      rw [← hp, ← hj₁, ← hj₂, ← Finset.sum_add_distrib]
    · rw [Fintype.mem_piFinset]
      intro i; exact Finset.mem_antidiagonal.mpr rfl
  · rintro ⟨j, c⟩ hm
    rw [Finset.mem_sigma] at hm
    dsimp only at hm
    have hc := Fintype.mem_piFinset.mp hm.2
    simp only [Sigma.mk.inj_iff]
    refine ⟨funext fun i => Finset.mem_antidiagonal.mp (hc i),
            heq_of_eq (funext fun i => Prod.eta (c i))⟩
  · rintro ⟨⟨p, j₁⟩, j₂⟩ hm
    rw [Finset.mem_sigma] at hm
    rw [Finset.mem_sigma] at hm
    dsimp only at hm
    have hj₁ := Finset.Nat.mem_antidiagonalTuple.mp hm.1.2
    have hj₂ := Finset.Nat.mem_antidiagonalTuple.mp hm.2
    simp only [Sigma.mk.inj_iff]
    exact ⟨⟨Prod.ext hj₁ hj₂, heq_of_eq (funext fun _ => rfl)⟩,
           heq_of_eq (funext fun _ => rfl)⟩
  · intro _ _; rfl

/-! ## Tensor product of polynomial families -/

namespace PolyFamily

variable {X Y X' Y' : TensorObj K d}

/-- Tensor (Kronecker) product of two polynomial families. For each mode `i` and index
`j`, the coefficient is the convolution `∑_{j₁+j₂=j} TensorProduct.map (Φ.A i j₁) (Ψ.A i j₂)`. -/
private noncomputable def tensorFam (Φ : PolyFamily X Y) (Ψ : PolyFamily X' Y') :
    PolyFamily (TensorObj.kron X X') (TensorObj.kron Y Y') where
  A := fun i =>
    Finsupp.onFinset
      (((Φ.A i).support ×ˢ (Ψ.A i).support).image (fun p => p.1 + p.2))
      (fun j => ∑ p ∈ Finset.antidiagonal j,
          TensorProduct.map (Φ.A i p.1) (Ψ.A i p.2))
      (fun j hj => by
        by_contra hmem
        apply hj
        refine Finset.sum_eq_zero ?_
        intro p hp
        rw [Finset.mem_antidiagonal] at hp
        by_contra hne
        apply hmem
        simp only [Finset.mem_image, Finset.mem_product, Finsupp.mem_support_iff]
        refine ⟨p, ⟨?_, ?_⟩, hp⟩
        · intro h1
          apply hne
          rw [h1]; exact TensorProduct.map_zero_left _
        · intro h2
          apply hne
          rw [h2]; exact TensorProduct.map_zero_right _)

private theorem tensorFam_A_apply (Φ : PolyFamily X Y) (Ψ : PolyFamily X' Y')
    (i : Fin d) (j : ℕ) :
    (Φ.tensorFam Ψ).A i j =
      ∑ p ∈ Finset.antidiagonal j,
        TensorProduct.map (Φ.A i p.1) (Ψ.A i p.2) :=
  rfl

/-- The `T^k` coefficient of a tensor product of polynomial families is the convolution
of the individual coefficients through `interchange`. -/
private theorem tensorFam_coeff_expand (Φ : PolyFamily X Y) (Ψ : PolyFamily X' Y') (k : ℕ) :
    (Φ.tensorFam Ψ).coeff k = ∑ p ∈ Finset.antidiagonal k,
      interchange (Φ.coeff p.1) (Ψ.coeff p.2) := by
  unfold coeff
  -- Step 1: unfold convolution inside `map` (definitional via tensorFam_A_apply)
  show ∑ j ∈ Finset.Nat.antidiagonalTuple d k,
      PiTensorProduct.map (fun i => ∑ p ∈ Finset.antidiagonal (j i),
        TensorProduct.map (Φ.A i p.1) (Ψ.A i p.2)) (TensorObj.kron Y Y').t = _
  -- Step 2: expand `map` of a sum via multilinearity
  simp_rw [map_sum_piFinset]
  -- Step 3: push application inside sum; `(kron Y Y').t = interchange Y.t Y'.t`
  show ∑ j ∈ Finset.Nat.antidiagonalTuple d k,
      (∑ c ∈ Fintype.piFinset (fun i => Finset.antidiagonal (j i)),
        PiTensorProduct.map (fun i => TensorProduct.map (Φ.A i (c i).1) (Ψ.A i (c i).2)))
          (interchange Y.t Y'.t) = _
  simp_rw [LinearMap.sum_apply, map_interchange]
  -- Step 4: reindex
  rw [sum_antidiagTuple_piFinset_antidiag
    (fun j₁ j₂ => interchange (PiTensorProduct.map (fun i => Φ.A i (j₁ i)) Y.t)
      (PiTensorProduct.map (fun i => Ψ.A i (j₂ i)) Y'.t))]
  -- Step 5: pull sums through interchange (bilinearity)
  congr 1; ext ⟨p₁, p₂⟩; dsimp only; symm
  show interchange (Φ.coeff p₁) (Ψ.coeff p₂) = _
  unfold coeff
  simp_rw [map_sum, LinearMap.sum_apply]
  exact Finset.sum_comm

end PolyFamily

/-! ## Kronecker of two degenerations adds orders -/

/-- Kronecker product of two degenerations: orders add. -/
private theorem degeneratesOfOrder_kron {X₁ Y₁ X₂ Y₂ : TensorObj K d} {h₁ h₂ : ℕ}
    (hdeg₁ : DegeneratesOfOrder X₁ Y₁ h₁) (hdeg₂ : DegeneratesOfOrder X₂ Y₂ h₂) :
    DegeneratesOfOrder (TensorObj.kron X₁ X₂) (TensorObj.kron Y₁ Y₂) (h₁ + h₂) := by
  obtain ⟨Φ, hvan₁, hcoeff₁⟩ := hdeg₁
  obtain ⟨Ψ, hvan₂, hcoeff₂⟩ := hdeg₂
  refine ⟨Φ.tensorFam Ψ, ?_, ?_⟩
  · intro k hk
    rw [PolyFamily.tensorFam_coeff_expand]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    by_cases hcase : p.1 < h₁
    · rw [hvan₁ p.1 hcase]; exact (interchange (K := K)).map_zero₂ _
    · rw [not_lt] at hcase
      have hp2 : p.2 < h₂ := by omega
      rw [hvan₂ p.2 hp2]; exact map_zero _
  · rw [PolyFamily.tensorFam_coeff_expand, Finset.sum_eq_single (h₁, h₂)]
    · rw [hcoeff₁, hcoeff₂]; rfl
    · intro p hp hne
      rw [Finset.mem_antidiagonal] at hp
      by_cases hcase : p.1 < h₁
      · rw [hvan₁ p.1 hcase]; exact (interchange (K := K)).map_zero₂ _
      · rw [not_lt] at hcase
        have hp2 : p.2 < h₂ := by
          by_contra h2; rw [not_lt] at h2
          exact hne (Prod.ext (by omega) (by omega))
        rw [hvan₂ p.2 hp2]; exact map_zero _
    · intro hmem
      exact absurd (Finset.mem_antidiagonal.mpr (rfl : h₁ + h₂ = (h₁, h₂).1 + (h₁, h₂).2))
        hmem

/-! ## Restriction and its compatibility with degeneration -/

/-- `ofRestrict f` has `T^0` coefficient equal to `map f Y.t`. -/
private theorem PolyFamily.ofRestrict_coeff_zero {X Y : TensorObj K d}
    (f : ∀ i, Y.V i →ₗ[K] X.V i) :
    (PolyFamily.ofRestrict f : PolyFamily X Y).coeff 0 = PiTensorProduct.map f Y.t := by
  unfold PolyFamily.coeff PolyFamily.ofRestrict
  rw [Finset.Nat.antidiagonalTuple_zero_right, Finset.sum_singleton]
  have hfam : (fun i => (Finsupp.single (0 : ℕ) (f i)) ((0 : Fin d → ℕ) i)) = f := by
    funext i; rw [Pi.zero_apply, Finsupp.single_eq_same]
  rw [hfam]

/-- A restriction yields a degeneration of order `0`. -/
private theorem restrict_degeneratesOfOrder {X Y : TensorObj K d}
    (hRes : TensorObj.Restrict X Y) : DegeneratesOfOrder X Y 0 := by
  obtain ⟨f, hf⟩ := hRes
  refine ⟨PolyFamily.ofRestrict f, ?_, ?_⟩
  · intro k hk; exact absurd hk (Nat.not_lt_zero k)
  · rw [PolyFamily.ofRestrict_coeff_zero, hf]

/-- Degeneration is preserved by a restriction on the bigger (right) side. -/
private theorem degeneratesOfOrder_of_restrict_right {X Y Y' : TensorObj K d} {h : ℕ}
    (hRes : TensorObj.Restrict Y Y') (hdeg : DegeneratesOfOrder X Y h) :
    DegeneratesOfOrder X Y' h := by
  obtain ⟨g, hg⟩ := hRes
  obtain ⟨Φ, hvan, hcoeff⟩ := hdeg
  refine ⟨⟨fun i => (Φ.A i).mapRange (fun L => L.comp (g i)) (by simp)⟩, ?_, ?_⟩
  · intro k hk
    have hco : (PolyFamily.mk fun i => (Φ.A i).mapRange (fun L => L.comp (g i))
        (by simp) : PolyFamily X Y').coeff k = Φ.coeff k := by
      unfold PolyFamily.coeff
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Finsupp.mapRange_apply]
      rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hg]
    rw [hco]; exact hvan k hk
  · have hco : (PolyFamily.mk fun i => (Φ.A i).mapRange (fun L => L.comp (g i))
        (by simp) : PolyFamily X Y').coeff h = Φ.coeff h := by
      unfold PolyFamily.coeff
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Finsupp.mapRange_apply]
      rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hg]
    rw [hco, hcoeff]

/-- `I_{r₁} ⊗ I_{r₂}` restricts to `I_{r₁·r₂}`: a degeneration of order 0 from the
diagonal. We exhibit explicit per-mode linear maps sending the basis of `Fin(r₁·r₂)→K`
to the tensor-product basis `e_a ⊗ e_b`. -/
private theorem restrict_diag_kron (r₁ r₂ : ℕ) :
    TensorObj.Restrict (TensorObj.kron (TensorObj.diagObj K d r₁) (TensorObj.diagObj K d r₂))
      (TensorObj.diagObj K d (r₁ * r₂)) := by
  classical
  -- The per-mode linear map sending `e_c ↦ e_{(e.symm c).1} ⊗ e_{(e.symm c).2}`.
  set e : Fin r₁ × Fin r₂ ≃ Fin (r₁ * r₂) := finProdFinEquiv with he
  refine ⟨fun _ => ∑ c : Fin (r₁ * r₂),
    LinearMap.smulRight (LinearMap.proj c : (Fin (r₁ * r₂) → K) →ₗ[K] K)
      ((Pi.single (e.symm c).1 (1 : K) : Fin r₁ → K) ⊗ₜ[K]
       (Pi.single (e.symm c).2 (1 : K) : Fin r₂ → K)), ?_⟩
  -- Evaluate the per-mode map on a basis vector.
  have heval : ∀ (k : Fin (r₁ * r₂)),
      (∑ c : Fin (r₁ * r₂),
        LinearMap.smulRight (LinearMap.proj c : (Fin (r₁ * r₂) → K) →ₗ[K] K)
          ((Pi.single (e.symm c).1 (1 : K) : Fin r₁ → K) ⊗ₜ[K]
           (Pi.single (e.symm c).2 (1 : K) : Fin r₂ → K)))
        (Pi.single k (1 : K)) =
      (Pi.single (e.symm k).1 (1 : K) : Fin r₁ → K) ⊗ₜ[K]
        (Pi.single (e.symm k).2 (1 : K) : Fin r₂ → K) := by
    intro k
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply,
      LinearMap.proj_apply]
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
      (fun c _ hck => by rw [Pi.single_eq_of_ne hck, zero_smul])]
    simp
  -- Compute LHS = map (fun _ => g) (diagObj (r₁*r₂)).t  as  ∑ c, tprod (g e_c).
  show PiTensorProduct.map _ (TensorObj.diagObj K d (r₁ * r₂)).t = _
  have hLHS : PiTensorProduct.map (fun _ : Fin d => ∑ c : Fin (r₁ * r₂),
      LinearMap.smulRight (LinearMap.proj c : (Fin (r₁ * r₂) → K) →ₗ[K] K)
        ((Pi.single (e.symm c).1 (1 : K) : Fin r₁ → K) ⊗ₜ[K]
         (Pi.single (e.symm c).2 (1 : K) : Fin r₂ → K)))
        (TensorObj.diagObj K d (r₁ * r₂)).t =
      ∑ c : Fin (r₁ * r₂), tprod K (fun _ : Fin d =>
        (Pi.single (e.symm c).1 (1 : K) : Fin r₁ → K) ⊗ₜ[K]
          (Pi.single (e.symm c).2 (1 : K) : Fin r₂ → K)) := by
    show PiTensorProduct.map _
        (∑ c : Fin (r₁ * r₂), tprod K (fun _ => (Pi.single c 1 : Fin (r₁ * r₂) → K))) = _
    rw [map_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [PiTensorProduct.map_tprod]
    congr 1; ext i; exact heval c
  refine hLHS.trans ?_
  -- RHS = interchange (∑ e_a)(∑ e_b), written on the clean sums (defeq to `(kron..).t`)
  -- so `map_sum` fires; expand to a clean double sum `∑a ∑b tprod (e_a ⊗ e_b)`.
  rw [show (TensorObj.kron (TensorObj.diagObj K d r₁) (TensorObj.diagObj K d r₂)).t =
      interchange (∑ a : Fin r₁, tprod K (fun _ => (Pi.single a 1 : Fin r₁ → K)))
        (∑ b : Fin r₂, tprod K (fun _ => (Pi.single b 1 : Fin r₂ → K))) from rfl]
  -- Expand `interchange (∑a)(∑b)` to a clean double sum `∑ b ∑ a tprod (e_a ⊗ e_b)`.
  simp only [map_sum, LinearMap.sum_apply, interchange_tprod]
  -- Now RHS = `∑ b ∑ a tprod (e_a ⊗ e_b)`; reindex LHS over `Fin (r₁*r₂)`.
  rw [Finset.sum_comm]
  rw [← e.sum_comp (fun c => tprod K (fun _ : Fin d =>
        (Pi.single (e.symm c).1 (1 : K) : Fin r₁ → K) ⊗ₜ[K]
          (Pi.single (e.symm c).2 (1 : K) : Fin r₂ → K)))]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [he, Equiv.symm_apply_apply]

/-! ## Main theorem -/

/-- **Degeneration is multiplicative under Kronecker powers.** -/
theorem solution {K : Type u} [Field K] {d : ℕ} {X : TensorObj K d} {r h : ℕ}
    (hdeg : DegeneratesOfOrder X (TensorObj.diagObj K d r) h) (m : ℕ) :
    DegeneratesOfOrder (TensorObj.kronPow X m) (TensorObj.diagObj K d (r ^ m)) (m * h) := by
  induction m with
  | zero =>
    -- `kronPow X 0 = oneObj`, `diagObj (r^0) = diagObj 1`, order 0.
    simp only [Nat.zero_mul, pow_zero]
    -- Restriction `oneObj ≤ diagObj 1` (order-0 degeneration).
    apply restrict_degeneratesOfOrder
    -- Per-mode map `(Fin 1 → K) →ₗ K` sending `e_0 ↦ 1` is `proj 0`.
    refine ⟨fun _ => (LinearMap.proj (0 : Fin 1) : (Fin 1 → K) →ₗ[K] K), ?_⟩
    show PiTensorProduct.map _ (TensorObj.diagObj K d 1).t = (TensorObj.kronPow X 0).t
    have hL : PiTensorProduct.map (fun _ : Fin d =>
        (LinearMap.proj (0 : Fin 1) : (Fin 1 → K) →ₗ[K] K))
        (TensorObj.diagObj K d 1).t = tprod K (fun _ : Fin d => (1 : K)) := by
      show PiTensorProduct.map _
          (∑ c : Fin 1, tprod K (fun _ => (Pi.single c 1 : Fin 1 → K))) = _
      rw [map_sum, Fintype.sum_unique, PiTensorProduct.map_tprod]
      have : (fun _ : Fin d => (LinearMap.proj (0 : Fin 1) : (Fin 1 → K) →ₗ[K] K)
          (Pi.single (default : Fin 1) (1 : K) : Fin 1 → K)) = (fun _ : Fin d => (1 : K)) := by
        funext i
        rw [LinearMap.proj_apply, Subsingleton.elim (default : Fin 1) 0, Pi.single_eq_same]
      rw [this]
    exact hL
  | succ n ih =>
    -- `kronPow X (n+1) = kron X (kronPow X n)`, IH degenerates from `diagObj (r^n)`.
    -- Kron of `hdeg` (order h, from `diagObj r`) and `ih` (order n*h, from `diagObj (r^n)`)
    -- gives order `h + n*h = (n+1)*h` from `kron (diagObj r) (diagObj (r^n))`.
    have hkron := degeneratesOfOrder_kron hdeg ih
    -- Transport along the restriction `kron (diagObj r) (diagObj (r^n)) ≤ diagObj (r^(n+1))`.
    have hres : TensorObj.Restrict
        (TensorObj.kron (TensorObj.diagObj K d r) (TensorObj.diagObj K d (r ^ n)))
        (TensorObj.diagObj K d (r ^ (n + 1))) := by
      rw [pow_succ, mul_comm (r ^ n) r]
      exact restrict_diag_kron r (r ^ n)
    have hfin := degeneratesOfOrder_of_restrict_right hres hkron
    -- Match the goal: `kronPow X (n+1) = kron X (kronPow X n)`, order `h + n*h = (n+1)*h`.
    rw [show (n + 1) * h = h + n * h by ring]
    exact hfin

end MME

open MME in
/-- Top-level alias: the platform's prover looks for `solution`, not `MME.solution`. -/
theorem solution {K : Type u} [Field K] {d : ℕ} {X : TensorObj K d} {r h : ℕ}
    (hdeg : DegeneratesOfOrder X (TensorObj.diagObj K d r) h) (m : ℕ) :
    DegeneratesOfOrder (TensorObj.kronPow X m) (TensorObj.diagObj K d (r ^ m)) (m * h) :=
  MME.solution hdeg m
