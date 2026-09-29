-- Prove2me | solution 1 for mme_borderRank_kronPow_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-31T19:48:28.350495+00:00
-- url     : https://prove2.me/submissions/8b6ce5b4-9da5-4549-92cf-0ba4ed344f73

import Definitions.Def_mme_degeneration
import Definitions.Def_mme_tensor_rank
import Mathlib.Logic.Equiv.Fin.Basic

open MME PiTensorProduct TensorProduct BigOperators

universe u

set_option maxHeartbeats 1000000

namespace MME

variable {K : Type u} [Field K] {d : ℕ}

/-! ## Helper lemmas about `PiTensorProduct.map` and `interchange`

These are inlined from `Sol_mme_kronPow_degenerate.lean` because we may only edit this
file. They are private and used only to prove the main theorem below. -/

/-- `interchange` on pure tensors gives a pure tensor of tensor products. -/
private theorem brKron_interchange_tprod {ι : Type*} [Fintype ι] [DecidableEq ι]
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
private theorem brKron_map_interchange {ι : Type*} [Fintype ι] [DecidableEq ι]
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
      rw [brKron_interchange_tprod, PiTensorProduct.map_tprod, PiTensorProduct.map_tprod,
        PiTensorProduct.map_tprod, brKron_interchange_tprod]
      simp only [TensorProduct.map_tmul]
    | add x y ih1 ih2 =>
      simp only [map_add] at ih1 ih2 ⊢
      rw [ih1, ih2]
  | add x y ih1 ih2 =>
    simp only [map_add, LinearMap.add_apply, ih1, ih2]

/-- `PiTensorProduct.map` of a family of finite sums expands as a sum over the
product index set. -/
private theorem brKron_map_sum_piFinset {V W : Fin d → Type u}
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

/-- Reindexing of nested sums over antidiagonal tuples. -/
private theorem brKron_sum_antidiagTuple_piFinset_antidiag {β : Type*} [AddCommMonoid β]
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

/-- Tensor (Kronecker) product of two polynomial families. -/
private noncomputable def brKron_tensorFam (Φ : PolyFamily X Y) (Ψ : PolyFamily X' Y') :
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

private theorem brKron_tensorFam_A_apply (Φ : PolyFamily X Y) (Ψ : PolyFamily X' Y')
    (i : Fin d) (j : ℕ) :
    (Φ.brKron_tensorFam Ψ).A i j =
      ∑ p ∈ Finset.antidiagonal j,
        TensorProduct.map (Φ.A i p.1) (Ψ.A i p.2) :=
  rfl

/-- The `T^k` coefficient of a tensor product of polynomial families is the convolution
of the individual coefficients through `interchange`. -/
private theorem brKron_tensorFam_coeff_expand (Φ : PolyFamily X Y) (Ψ : PolyFamily X' Y')
    (k : ℕ) :
    (Φ.brKron_tensorFam Ψ).coeff k = ∑ p ∈ Finset.antidiagonal k,
      interchange (Φ.coeff p.1) (Ψ.coeff p.2) := by
  unfold coeff
  show ∑ j ∈ Finset.Nat.antidiagonalTuple d k,
      PiTensorProduct.map (fun i => ∑ p ∈ Finset.antidiagonal (j i),
        TensorProduct.map (Φ.A i p.1) (Ψ.A i p.2)) (TensorObj.kron Y Y').t = _
  simp_rw [brKron_map_sum_piFinset]
  show ∑ j ∈ Finset.Nat.antidiagonalTuple d k,
      (∑ c ∈ Fintype.piFinset (fun i => Finset.antidiagonal (j i)),
        PiTensorProduct.map (fun i => TensorProduct.map (Φ.A i (c i).1) (Ψ.A i (c i).2)))
          (interchange Y.t Y'.t) = _
  simp_rw [LinearMap.sum_apply, brKron_map_interchange]
  rw [brKron_sum_antidiagTuple_piFinset_antidiag
    (fun j₁ j₂ => interchange (PiTensorProduct.map (fun i => Φ.A i (j₁ i)) Y.t)
      (PiTensorProduct.map (fun i => Ψ.A i (j₂ i)) Y'.t))]
  congr 1; ext ⟨p₁, p₂⟩; dsimp only; symm
  show interchange (Φ.coeff p₁) (Ψ.coeff p₂) = _
  unfold coeff
  simp_rw [map_sum, LinearMap.sum_apply]
  exact Finset.sum_comm

end PolyFamily

/-! ## Kronecker of two degenerations adds orders -/

private theorem brKron_degeneratesOfOrder_kron {X₁ Y₁ X₂ Y₂ : TensorObj K d} {h₁ h₂ : ℕ}
    (hdeg₁ : DegeneratesOfOrder X₁ Y₁ h₁) (hdeg₂ : DegeneratesOfOrder X₂ Y₂ h₂) :
    DegeneratesOfOrder (TensorObj.kron X₁ X₂) (TensorObj.kron Y₁ Y₂) (h₁ + h₂) := by
  obtain ⟨Φ, hvan₁, hcoeff₁⟩ := hdeg₁
  obtain ⟨Ψ, hvan₂, hcoeff₂⟩ := hdeg₂
  refine ⟨Φ.brKron_tensorFam Ψ, ?_, ?_⟩
  · intro k hk
    rw [PolyFamily.brKron_tensorFam_coeff_expand]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    by_cases hcase : p.1 < h₁
    · rw [hvan₁ p.1 hcase]; exact (interchange (K := K)).map_zero₂ _
    · rw [not_lt] at hcase
      have hp2 : p.2 < h₂ := by omega
      rw [hvan₂ p.2 hp2]; exact map_zero _
  · rw [PolyFamily.brKron_tensorFam_coeff_expand, Finset.sum_eq_single (h₁, h₂)]
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
private theorem brKron_ofRestrict_coeff_zero {X Y : TensorObj K d}
    (f : ∀ i, Y.V i →ₗ[K] X.V i) :
    (PolyFamily.ofRestrict f : PolyFamily X Y).coeff 0 = PiTensorProduct.map f Y.t := by
  unfold PolyFamily.coeff PolyFamily.ofRestrict
  rw [Finset.Nat.antidiagonalTuple_zero_right, Finset.sum_singleton]
  have hfam : (fun i => (Finsupp.single (0 : ℕ) (f i)) ((0 : Fin d → ℕ) i)) = f := by
    funext i; rw [Pi.zero_apply, Finsupp.single_eq_same]
  rw [hfam]

/-- A restriction yields a degeneration of order `0`. -/
private theorem brKron_restrict_degeneratesOfOrder {X Y : TensorObj K d}
    (hRes : TensorObj.Restrict X Y) : DegeneratesOfOrder X Y 0 := by
  obtain ⟨f, hf⟩ := hRes
  refine ⟨PolyFamily.ofRestrict f, ?_, ?_⟩
  · intro k hk; exact absurd hk (Nat.not_lt_zero k)
  · rw [brKron_ofRestrict_coeff_zero, hf]

/-- Degeneration is preserved by a restriction on the bigger (right) side. -/
private theorem brKron_degeneratesOfOrder_of_restrict_right {X Y Y' : TensorObj K d} {h : ℕ}
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

/-- `I_{r₁} ⊗ I_{r₂}` restricts to `I_{r₁·r₂}`. -/
private theorem brKron_restrict_diag_kron (r₁ r₂ : ℕ) :
    TensorObj.Restrict (TensorObj.kron (TensorObj.diagObj K d r₁) (TensorObj.diagObj K d r₂))
      (TensorObj.diagObj K d (r₁ * r₂)) := by
  classical
  set e : Fin r₁ × Fin r₂ ≃ Fin (r₁ * r₂) := finProdFinEquiv with he
  refine ⟨fun _ => ∑ c : Fin (r₁ * r₂),
    LinearMap.smulRight (LinearMap.proj c : (Fin (r₁ * r₂) → K) →ₗ[K] K)
      ((Pi.single (e.symm c).1 (1 : K) : Fin r₁ → K) ⊗ₜ[K]
       (Pi.single (e.symm c).2 (1 : K) : Fin r₂ → K)), ?_⟩
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
  rw [show (TensorObj.kron (TensorObj.diagObj K d r₁) (TensorObj.diagObj K d r₂)).t =
      interchange (∑ a : Fin r₁, tprod K (fun _ => (Pi.single a 1 : Fin r₁ → K)))
        (∑ b : Fin r₂, tprod K (fun _ => (Pi.single b 1 : Fin r₂ → K))) from rfl]
  simp only [map_sum, LinearMap.sum_apply, brKron_interchange_tprod]
  rw [Finset.sum_comm]
  rw [← e.sum_comp (fun c => tprod K (fun _ : Fin d =>
        (Pi.single (e.symm c).1 (1 : K) : Fin r₁ → K) ⊗ₜ[K]
          (Pi.single (e.symm c).2 (1 : K) : Fin r₂ → K)))]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [he, Equiv.symm_apply_apply]

/-! ## Helper: degeneration is multiplicative under Kronecker powers (order-tracked form) -/

/-- The order-tracked Kronecker-power degeneration. Adapted from `Sol_mme_kronPow_degenerate`. -/
private theorem brKron_kronPow_aux {X : TensorObj K d} {r h : ℕ}
    (hdeg : DegeneratesOfOrder X (TensorObj.diagObj K d r) h) (m : ℕ) :
    DegeneratesOfOrder (TensorObj.kronPow X m) (TensorObj.diagObj K d (r ^ m)) (m * h) := by
  induction m with
  | zero =>
    simp only [Nat.zero_mul, pow_zero]
    apply brKron_restrict_degeneratesOfOrder
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
    have hkron := brKron_degeneratesOfOrder_kron hdeg ih
    have hres : TensorObj.Restrict
        (TensorObj.kron (TensorObj.diagObj K d r) (TensorObj.diagObj K d (r ^ n)))
        (TensorObj.diagObj K d (r ^ (n + 1))) := by
      rw [pow_succ, mul_comm (r ^ n) r]
      exact brKron_restrict_diag_kron r (r ^ n)
    have hfin := brKron_degeneratesOfOrder_of_restrict_right hres hkron
    rw [show (n + 1) * h = h + n * h by ring]
    exact hfin

end MME

open MME

universe v

/-- **Border rank is multiplicative under Kronecker powers.**

For any order-`d` tensor object `X` with border rank at most `r` (i.e.
`Degenerates X (diagObj K d r)`), the `N`-fold Kronecker power
`X.kronPow N` has border rank at most `r^N`:

  `Degenerates X (diagObj K d r)  →  Degenerates (X.kronPow N) (diagObj K d (r^N))`.

Proved by induction on `N`, using Kronecker multiplicativity of polynomial families
and the order-0 degeneration `I_{r₁} ⊗ I_{r₂} ≤ I_{r₁·r₂}`. -/
theorem solution {K : Type u} [Field K] {d : ℕ}
    (X : TensorObj K d) (N r : ℕ)
    (h : Degenerates X (TensorObj.diagObj K d r)) :
    Degenerates (X.kronPow N) (TensorObj.diagObj K d (r ^ N)) := by
  obtain ⟨h0, hdeg⟩ := h
  exact ⟨N * h0, brKron_kronPow_aux hdeg N⟩
