-- Prove2me | solution 1 for mme_flatteningRank_MMObj_ca
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-06-05T03:29:01.89656+00:00
-- url     : https://prove2.me/submissions/2bf58932-c1a0-4f2c-881f-ed7014232e5f

import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_mme_omega
import Definitions.Def_mme_tensor
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_flattening
import Theorems.Thm_mme_flatteningRank_MMObj_ca

/-!
# `c*a ≤ flatteningRank σ_2 (MMObj K a b c)` for `b ≥ 1`

Mode-2 cyclic analogue of `Sol_mme_flatteningRank_MMObj_ab`. We construct `c*a` linearly
independent vectors in the range of the mode-2 flattening map.

For each (k₀, i₀) ∈ Fin c × Fin a, take the left-block basis dual at `(k₀, i₀)`. Its
image under the flattening map equals `∑_j R_{i₀,j,k₀}`, where R is the right-block
pure tensor with mode-0 entry `e_{(i₀,j)}` and mode-1 entry `e_{(j,k₀)}`. These images
for different (k₀, i₀) have disjoint basis support, so they're linearly independent
when b ≥ 1. -/

set_option maxHeartbeats 1600000

universe u

open PiTensorProduct TensorProduct BigOperators Module

namespace MMEFlatteningRankMMObjCaSol

open MME

variable {K : Type u} [Field K]

section MMObj_ca

/-- Alias for `split2`. -/
private noncomputable abbrev σ2 : Split (Fin 3) := split2

/-- `σ2.S = {2}` has a unique element. -/
private instance σ2_S_subsingleton : Subsingleton (σ2 : Split (Fin 3)).S := by
  refine ⟨fun x y => ?_⟩
  ext
  have hx : (x : Fin 3) ∈ ({(2 : Fin 3)} : Finset (Fin 3)) := x.2
  have hy : (y : Fin 3) ∈ ({(2 : Fin 3)} : Finset (Fin 3)) := y.2
  rw [Finset.mem_singleton] at hx hy
  rw [hx, hy]

/-- The element `2 : Fin 3` packaged as a member of `σ2.S = {2}`. -/
private def sTwoL : (σ2 : Split (Fin 3)).S :=
  ⟨(2 : Fin 3), by simp [σ2, split2]⟩

/-- `σ2.S` is nonempty. -/
private instance σ2_S_nonempty : Nonempty (σ2 : Split (Fin 3)).S := ⟨sTwoL⟩

/-- Decidable equality on `σ2.S`. -/
private instance σ2_S_decEq : DecidableEq (σ2 : Split (Fin 3)).S := by
  intro x y
  exact Decidable.isTrue (Subsingleton.elim _ _)

/-- The element `2 : Fin 3` is in `σ2.S`. -/
private lemma sTwoL_val : (sTwoL : (σ2 : Split (Fin 3)).S).val = 2 := rfl

/-- For any `s ∈ Sc σ2`, `s.val ≠ 2`. -/
private lemma sc_ne_two (s : Sc (σ2 : Split (Fin 3))) : (s.val : Fin 3) ≠ 2 := by
  intro h
  have hm : (s.val : Fin 3) ∈ (σ2 : Split (Fin 3)).Sᶜ := s.2
  rw [h] at hm
  have h2 : (2 : Fin 3) ∈ (σ2 : Split (Fin 3)).S := by
    show (2 : Fin 3) ∈ ({(2 : Fin 3)} : Finset (Fin 3))
    rw [Finset.mem_singleton]
  exact Finset.mem_compl.mp hm h2

/-- The basis-index type for each mode of `MMObj K a b c`, uniformly on `Fin 3`. -/
private def MMIdx (a b c : ℕ) : Fin 3 → Type
  | ⟨0, _⟩ => Fin a × Fin b
  | ⟨1, _⟩ => Fin b × Fin c
  | ⟨2, _⟩ => Fin c × Fin a
  | ⟨_+3, h⟩ => absurd h (by omega)

private instance MMIdx_fintype (a b c : ℕ) (i : Fin 3) : Fintype (MMIdx a b c i) := by
  match i with
  | ⟨0, _⟩ => exact inferInstanceAs (Fintype (Fin a × Fin b))
  | ⟨1, _⟩ => exact inferInstanceAs (Fintype (Fin b × Fin c))
  | ⟨2, _⟩ => exact inferInstanceAs (Fintype (Fin c × Fin a))

private instance MMIdx_decEq (a b c : ℕ) (i : Fin 3) : DecidableEq (MMIdx a b c i) := by
  match i with
  | ⟨0, _⟩ => exact inferInstanceAs (DecidableEq (Fin a × Fin b))
  | ⟨1, _⟩ => exact inferInstanceAs (DecidableEq (Fin b × Fin c))
  | ⟨2, _⟩ => exact inferInstanceAs (DecidableEq (Fin c × Fin a))

/-- Per-mode basis (matching `MMSpace`). -/
private noncomputable def MMBasis (K : Type u) [Field K] (a b c : ℕ) :
    ∀ i : Fin 3, Basis (MMIdx a b c i) K (MMSpace K a b c i) := by
  intro i
  match i with
  | ⟨0, _⟩ => exact Pi.basisFun K (Fin a × Fin b)
  | ⟨1, _⟩ => exact Pi.basisFun K (Fin b × Fin c)
  | ⟨2, _⟩ => exact Pi.basisFun K (Fin c × Fin a)

/-- Left-block basis: indexed by `σ2.S → Fin c × Fin a`. -/
private noncomputable def bL (a b c : ℕ) :
    Basis ((σ2 : Split (Fin 3)).S → Fin c × Fin a) K
      (PiTensorProduct K (fun i : (σ2 : Split (Fin 3)).S =>
        (MMObj K a b c).V i.val)) :=
  Basis.piTensorProduct (fun i : (σ2 : Split (Fin 3)).S =>
    (show (MMIdx a b c i.val) = (Fin c × Fin a) by
      have hx2 : (i : Fin 3) = 2 := Finset.mem_singleton.mp i.2
      rw [hx2]; rfl) ▸ MMBasis K a b c i.val)

/-- Right-block basis: indexed by `∀ s : Sc σ2, MMIdx a b c s.val`. -/
private noncomputable def bR (a b c : ℕ) :
    Basis (∀ s : Sc (σ2 : Split (Fin 3)), MMIdx a b c s.val) K
      (PiTensorProduct K (fun i : Sc (σ2 : Split (Fin 3)) =>
        (MMObj K a b c).V i.val)) :=
  Basis.piTensorProduct (fun s : Sc (σ2 : Split (Fin 3)) => MMBasis K a b c s.val)

/-- The right-block basis index `g_{k₀,i₀,j}` corresponding to the pure tensor with
mode-0 entry `e_{(i₀,j)}` and mode-1 entry `e_{(j,k₀)}`. -/
private noncomputable def gR (a b c : ℕ)
    (k₀ : Fin c) (i₀ : Fin a) (j : Fin b) :
    ∀ s : Sc (σ2 : Split (Fin 3)), MMIdx a b c s.val := fun s =>
  match h : (s.val : Fin 3) with
  | ⟨0, _⟩ => (i₀, j)
  | ⟨1, _⟩ => (j, k₀)
  | ⟨2, _⟩ => absurd h (sc_ne_two s)

/-- The candidate vector `vec (k₀, i₀)` in `V_right`: sum of right-block basis tensors
indexed by `gR k₀ i₀ j` for `j ∈ Fin b`. -/
private noncomputable def vec (a b c : ℕ) (ki : Fin c × Fin a) :
    PiTensorProduct K (fun i : Sc (σ2 : Split (Fin 3)) => (MMObj K a b c).V i.val) :=
  ∑ j : Fin b, bR a b c (gR a b c ki.1 ki.2 j)

/-- A concrete element of `Sc σ2` with value `0`. -/
private noncomputable def sZeroC : Sc (σ2 : Split (Fin 3)) :=
  ⟨(0 : Fin 3), by
    show (0 : Fin 3) ∈ (σ2 : Split (Fin 3)).Sᶜ
    rw [Finset.mem_compl]
    intro h
    have : (0 : Fin 3) ∈ ({(2 : Fin 3)} : Finset (Fin 3)) := h
    have h20 : (0 : Fin 3) = 2 := Finset.mem_singleton.mp this
    exact absurd h20 (by decide)⟩

/-- A concrete element of `Sc σ2` with value `1`. -/
private noncomputable def sOneC : Sc (σ2 : Split (Fin 3)) :=
  ⟨(1 : Fin 3), by
    show (1 : Fin 3) ∈ (σ2 : Split (Fin 3)).Sᶜ
    rw [Finset.mem_compl]
    intro h
    have : (1 : Fin 3) ∈ ({(2 : Fin 3)} : Finset (Fin 3)) := h
    have h21 : (1 : Fin 3) = 2 := Finset.mem_singleton.mp this
    exact absurd h21 (by decide)⟩

private lemma sZeroC_val : (sZeroC : Sc (σ2 : Split (Fin 3))).val = (0 : Fin 3) := rfl
private lemma sOneC_val : (sOneC : Sc (σ2 : Split (Fin 3))).val = (1 : Fin 3) := rfl

/-- `gR k₀ i₀ j` evaluated at `sZeroC` (mode-0 slot) gives `(i₀, j)`. -/
private lemma gR_at_sZeroC (a b c : ℕ) (k₀ : Fin c) (i₀ : Fin a) (j : Fin b) :
    (gR a b c k₀ i₀ j sZeroC : MMIdx a b c (sZeroC : Sc (σ2 : Split (Fin 3))).val) = (i₀, j) := by
  unfold gR
  rfl

/-- `gR k₀ i₀ j` evaluated at `sOneC` (mode-1 slot) gives `(j, k₀)`. -/
private lemma gR_at_sOneC (a b c : ℕ) (k₀ : Fin c) (i₀ : Fin a) (j : Fin b) :
    (gR a b c k₀ i₀ j sOneC : MMIdx a b c (sOneC : Sc (σ2 : Split (Fin 3))).val) = (j, k₀) := by
  unfold gR
  rfl

/-- The combined index `(ki, j) ↦ gR ki.1 ki.2 j` is injective. -/
private lemma gR_injective (a b c : ℕ) :
    Function.Injective (fun (p : (Fin c × Fin a) × Fin b) =>
      gR a b c p.1.1 p.1.2 p.2) := by
  rintro ⟨⟨k₀, i₀⟩, j⟩ ⟨⟨k₀', i₀'⟩, j'⟩ h
  simp only at h
  -- evaluate at sZeroC to get (i₀, j) = (i₀', j')
  have h1 : gR a b c k₀ i₀ j sZeroC = gR a b c k₀' i₀' j' sZeroC := by
    rw [h]
  rw [gR_at_sZeroC, gR_at_sZeroC] at h1
  -- evaluate at sOneC to get (j, k₀) = (j', k₀')
  have h2 : gR a b c k₀ i₀ j sOneC = gR a b c k₀' i₀' j' sOneC := by
    rw [h]
  rw [gR_at_sOneC, gR_at_sOneC] at h2
  obtain ⟨hi, hj⟩ := Prod.mk.inj h1
  obtain ⟨_, hk⟩ := Prod.mk.inj h2
  simp [hi, hj, hk]

/-- For different `ki ≠ ki'`, the images `{gR ki.1 ki.2 j | j}` and
`{gR ki'.1 ki'.2 j | j}` are disjoint. -/
private lemma gR_disjoint (a b c : ℕ) {ki ki' : Fin c × Fin a} (hne : ki ≠ ki')
    (j j' : Fin b) :
    gR a b c ki.1 ki.2 j ≠ gR a b c ki'.1 ki'.2 j' := by
  intro h
  apply hne
  -- evaluate at sZeroC for i-component
  have h1 : gR a b c ki.1 ki.2 j sZeroC = gR a b c ki'.1 ki'.2 j' sZeroC := by rw [h]
  rw [gR_at_sZeroC, gR_at_sZeroC] at h1
  obtain ⟨hi, _⟩ := Prod.mk.inj h1
  -- evaluate at sOneC for k-component
  have h2 : gR a b c ki.1 ki.2 j sOneC = gR a b c ki'.1 ki'.2 j' sOneC := by rw [h]
  rw [gR_at_sOneC, gR_at_sOneC] at h2
  obtain ⟨_, hk⟩ := Prod.mk.inj h2
  exact Prod.ext hk hi

/-- **Linear independence of `vec`.** Uses dual functionals:
the basis coord `bR.coord (gR ki.1 ki.2 ⟨0, hb⟩)` evaluates to 1 on `vec ki` and to 0
on `vec ki'` for `ki ≠ ki'`. -/
private lemma vec_linearIndependent (a b c : ℕ) (hb : 1 ≤ b) :
    LinearIndependent K (vec (K := K) a b c) := by
  let φ : Fin c × Fin a → Dual K
      (PiTensorProduct K (fun i : Sc (σ2 : Split (Fin 3)) =>
        (MMObj K a b c).V i.val)) :=
    fun ki => (bR a b c).coord (gR a b c ki.1 ki.2 ⟨0, hb⟩)
  refine LinearIndependent.of_pairwise_dual_eq_zero_one (v := vec a b c) (f := φ) ?_ ?_
  · intro ki ki' hne
    show φ ki (vec a b c ki') = 0
    unfold vec
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [Basis.coord_apply, Basis.repr_self_apply]
    rw [if_neg]
    intro h
    exact gR_disjoint a b c (Ne.symm hne) j ⟨0, hb⟩ h
  · intro ki
    show φ ki (vec a b c ki) = 1
    unfold vec
    rw [map_sum]
    rw [Finset.sum_eq_single (⟨0, hb⟩ : Fin b)]
    · rw [Basis.coord_apply, Basis.repr_self_apply, if_pos rfl]
    · intro j _ hj
      rw [Basis.coord_apply, Basis.repr_self_apply, if_neg]
      intro h
      have hinj := gR_injective a b c
      have : ((ki, j) : (Fin c × Fin a) × Fin b) = ((ki, ⟨0, hb⟩) : (Fin c × Fin a) × Fin b) := by
        apply hinj
        exact h
      have := (Prod.mk.inj this).2
      exact hj this
    · intro h; exact absurd (Finset.mem_univ _) h

/-! ### Step 2: Each `vec ki` is in the range of the flattening map. -/

/-- The dual functional that "picks out coordinate `ki`" via the singleton
identification of the left block. -/
private noncomputable def dualL (a b c : ℕ) (ki : Fin c × Fin a) :
    Dual K (PiTensorProduct K (fun i : (σ2 : Split (Fin 3)).S =>
      (MMObj K a b c).V i.val)) :=
  (LinearMap.proj ki : (Fin c × Fin a → K) →ₗ[K] K).comp
    ((PiTensorProduct.subsingletonEquiv sTwoL).toLinearMap :
      PiTensorProduct K (fun i : (σ2 : Split (Fin 3)).S =>
        (MMObj K a b c).V i.val) →ₗ[K] (Fin c × Fin a → K))

/-- `dualL ki` applied to a pure tensor `tprod K v` evaluates `v sTwoL` at `ki`. -/
private lemma dualL_tprod (a b c : ℕ) (ki : Fin c × Fin a)
    (v : ∀ s : (σ2 : Split (Fin 3)).S, (MMObj K a b c).V s.val) :
    dualL a b c ki (tprod K v) = (v sTwoL : Fin c × Fin a → K) ki := by
  unfold dualL
  rw [LinearMap.comp_apply, LinearMap.proj_apply]
  have h : (PiTensorProduct.subsingletonEquiv sTwoL : PiTensorProduct K
      (fun i : (σ2 : Split (Fin 3)).S => (MMObj K a b c).V i.val) ≃ₗ[K]
      (MMObj K a b c).V (sTwoL : (σ2 : Split (Fin 3)).S).val) (tprod K v) =
      v sTwoL :=
    PiTensorProduct.subsingletonEquiv_apply_tprod _ _
  show (PiTensorProduct.subsingletonEquiv sTwoL) (tprod K v) ki = v sTwoL ki
  rw [h]

/-- The mode-wise data function for the (i, j, k) term of `MMTensor K a b c`. -/
private noncomputable def modeData (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    ∀ s : Fin 3, MMSpace K a b c s := fun s =>
  match s with
  | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin a × Fin b → K)
  | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin b × Fin c → K)
  | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin c × Fin a → K)

/-- `MMTensor K a b c` written as a triple sum using `modeData`. -/
private lemma MMTensor_eq_sum (a b c : ℕ) :
    MMTensor K a b c = ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
      tprod K (modeData (K := K) a b c i j k) := by
  rfl

/-- The "left" tensor of the (i, j, k) term after `splitTensorEquiv σ2`. -/
private noncomputable def Lterm (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    PiTensorProduct K (fun s : (σ2 : Split (Fin 3)).S => (MMObj K a b c).V s.val) :=
  tprod K (fun s : (σ2 : Split (Fin 3)).S => modeData a b c i j k s.val)

/-- The "right" tensor of the (i, j, k) term after `splitTensorEquiv σ2`. -/
private noncomputable def Rterm (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    PiTensorProduct K (fun s : Sc (σ2 : Split (Fin 3)) => (MMObj K a b c).V s.val) :=
  tprod K (fun s : Sc (σ2 : Split (Fin 3)) => modeData a b c i j k s.val)

/-- `splitTensorEquiv` of one pure term decomposes into `Lterm ⊗ₜ Rterm`. -/
private lemma splitTensorEquiv_term (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    splitTensorEquiv σ2 (tprod K (modeData (K := K) a b c i j k))
      = Lterm a b c i j k ⊗ₜ[K] Rterm a b c i j k :=
  splitTensorEquiv_tprod _ _

/-- The `dualL ki` value on `Lterm i j k` is `δ_{(k,i) = ki}`. -/
private lemma dualL_Lterm (a b c : ℕ) (ki : Fin c × Fin a)
    (i : Fin a) (j : Fin b) (k : Fin c) :
    dualL a b c ki (Lterm a b c i j k) = if (k, i) = ki then (1 : K) else 0 := by
  unfold Lterm
  rw [dualL_tprod]
  show (modeData (K := K) a b c i j k (sTwoL : (σ2 : Split (Fin 3)).S).val :
    Fin c × Fin a → K) ki = if (k, i) = ki then (1 : K) else 0
  rw [show modeData (K := K) a b c i j k (sTwoL : (σ2 : Split (Fin 3)).S).val =
      (Pi.single (k, i) 1 : Fin c × Fin a → K) from rfl]
  rw [Pi.single_apply]
  by_cases h : ki = (k, i)
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- `Rterm i j k = bR (gR k i j)`. -/
private lemma Rterm_eq_bR (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    (Rterm (K := K) a b c i j k) = bR (K := K) a b c (gR a b c k i j) := by
  unfold Rterm bR
  rw [Basis.piTensorProduct_apply]
  congr 1
  funext s
  show modeData (K := K) a b c i j k s.val = MMBasis K a b c s.val (gR a b c k i j s)
  rcases s with ⟨sv, hsv⟩
  have hne : sv ≠ 2 := sc_ne_two ⟨sv, hsv⟩
  match sv, hne with
  | ⟨0, hsv0⟩, _ =>
    show (Pi.single (i, j) 1 : Fin a × Fin b → K) =
      MMBasis K a b c (⟨0, hsv0⟩ : Fin 3) (gR a b c k i j ⟨⟨0, hsv0⟩, hsv⟩)
    show (Pi.single (i, j) 1 : Fin a × Fin b → K) =
      Pi.basisFun K (Fin a × Fin b) (gR a b c k i j ⟨⟨0, hsv0⟩, hsv⟩)
    rw [Pi.basisFun_apply]
    rfl
  | ⟨1, hsv1⟩, _ =>
    show (Pi.single (j, k) 1 : Fin b × Fin c → K) =
      MMBasis K a b c (⟨1, hsv1⟩ : Fin 3) (gR a b c k i j ⟨⟨1, hsv1⟩, hsv⟩)
    show (Pi.single (j, k) 1 : Fin b × Fin c → K) =
      Pi.basisFun K (Fin b × Fin c) (gR a b c k i j ⟨⟨1, hsv1⟩, hsv⟩)
    rw [Pi.basisFun_apply]
    rfl
  | ⟨2, _⟩, h => exact absurd rfl h

/-- The key formula expressing `flatteningMap σ2 (MMObj K a b c) (dualL ki)` as
`∑_{i,j,k} δ_{(k,i)=ki} • bR (gR k i j) = vec ki`. -/
private lemma flatteningMap_MMObj_dualL_eq_vec (a b c : ℕ) (ki : Fin c × Fin a) :
    flatteningMap σ2 (MMObj K a b c) (dualL a b c ki) = vec a b c ki := by
  unfold flatteningMap
  show tensorToDualHom K _ _ (splitTensorEquiv σ2 (MMTensor K a b c)) (dualL a b c ki) =
    vec a b c ki
  rw [MMTensor_eq_sum]
  rw [show splitTensorEquiv σ2 (∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        tprod K (modeData (K := K) a b c i j k))
      = ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        Lterm a b c i j k ⊗ₜ[K] Rterm a b c i j k from ?_]
  swap
  · simp only [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact splitTensorEquiv_term a b c i j k
  have hreduce : ((tensorToDualHom K
      (PiTensorProduct K (fun s : (σ2 : Split (Fin 3)).S => (MMObj K a b c).V s.val))
      (PiTensorProduct K (fun s : Sc (σ2 : Split (Fin 3)) => (MMObj K a b c).V s.val)))
      (∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        Lterm a b c i j k ⊗ₜ[K] Rterm a b c i j k)) (dualL a b c ki) =
      ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        dualL (K := K) a b c ki (Lterm a b c i j k) • Rterm (K := K) a b c i j k := by
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [tensorToDualHom_tmul]
  change ((tensorToDualHom K
      (PiTensorProduct K (fun s : (σ2 : Split (Fin 3)).S => (MMObj K a b c).V s.val))
      (PiTensorProduct K (fun s : Sc (σ2 : Split (Fin 3)) => (MMObj K a b c).V s.val)))
      (∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        Lterm a b c i j k ⊗ₜ[K] Rterm a b c i j k)) (dualL a b c ki) = _
  rw [hreduce]
  simp_rw [dualL_Lterm]
  simp_rw [Rterm_eq_bR]
  -- Goal:
  -- ∑ i, ∑ j, ∑ k, (if (k,i) = ki then 1 else 0) • bR (gR k i j) = vec ki
  -- vec ki = ∑_j bR (gR ki.1 ki.2 j).
  -- For fixed j, the inner ∑_{i,k} selects (k,i) = ki.
  -- Strategy: swap sums; collapse i,k for each j.
  unfold vec
  -- Swap ∑_i ∑_j ∑_k → ∑_j (∑_i ∑_k) — Finset.sum_comm.
  rw [Finset.sum_comm]
  -- Now: ∑ j, ∑ i, ∑ k, (if (k,i) = ki then 1 else 0) • bR (gR k i j) = ∑ j, bR (gR ki.1 ki.2 j)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- For each j, collapse the (i, k) double sum.
  rw [Finset.sum_comm]
  -- Now: ∑ k, ∑ i, (if (k,i) = ki then 1 else 0) • bR (gR k i j) = bR (gR ki.1 ki.2 j)
  rw [Finset.sum_eq_single ki.1]
  · rw [Finset.sum_eq_single ki.2]
    · rw [if_pos rfl, one_smul]
    · intro i _ hi
      rw [if_neg, zero_smul]
      intro h
      apply hi
      exact (Prod.mk.inj h).2
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro k _ hk
    rw [Finset.sum_eq_zero]
    intro i _
    rw [if_neg, zero_smul]
    intro h
    apply hk
    exact (Prod.mk.inj h).1
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **`vec ki ∈ range (flatteningMap σ2 (MMObj K a b c))`.** -/
private lemma vec_mem_range (a b c : ℕ) (ki : Fin c × Fin a) :
    vec a b c ki ∈ LinearMap.range (flatteningMap σ2 (MMObj K a b c)) := by
  exact ⟨dualL a b c ki, flatteningMap_MMObj_dualL_eq_vec a b c ki⟩

end MMObj_ca

end MMEFlatteningRankMMObjCaSol

/-! ### Main result (top-level for platform upload) -/

open MMEFlatteningRankMMObjCaSol MME

/-- The mode-2 flattening rank of `MMObj K a b c` is at least `c * a` when `b ≥ 1`.

Proof: we construct `c * a` linearly independent vectors `vec ki` for `ki ∈ Fin c × Fin a`
in the range of the flattening map. Each `vec ki = ∑_j bR (gR ki.1 ki.2 j)` is a sum of
right-block basis tensors, and the index map `(ki, j) ↦ gR ki.1 ki.2 j` is injective;
combined with `b ≥ 1`, this yields linear independence. -/
theorem solution {K : Type u} [Field K] (a b c : ℕ) (hb : 1 ≤ b) :
    c * a ≤ MME.flatteningRank MME.split2 (MME.MMObj K a b c) := by
  unfold flatteningRank
  set V_right := PiTensorProduct K (fun i : Sc (σ2 : Split (Fin 3)) =>
    (MMObj K a b c).V i.val) with hVright
  haveI : FiniteDimensional K V_right :=
    Module.Finite.of_basis (bR a b c)
  set rangeFM := LinearMap.range (flatteningMap σ2 (MMObj K a b c)) with hrangeFM
  let vecInRange : Fin c × Fin a → rangeFM := fun ki =>
    ⟨vec a b c ki, vec_mem_range a b c ki⟩
  have hLI : LinearIndependent K vecInRange := by
    have hLI₀ : LinearIndependent K (vec (K := K) a b c) :=
      vec_linearIndependent a b c hb
    exact hLI₀.of_comp rangeFM.subtype
  have hcard : Fintype.card (Fin c × Fin a) = c * a := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have := hLI.fintype_card_le_finrank (R := K) (M := rangeFM)
  rw [hcard] at this
  exact this
