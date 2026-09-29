-- Prove2me | solution 1 for mme_more_asymmetry_finite_recursive_assembly
-- status  : ACCEPTED   (disprove)
-- author  : @Robertboy18
-- created : 2026-09-22T07:01:42.354465+00:00
-- url     : https://prove2.me/submissions/3fbe3b7c-80b0-45b8-924a-6b8abc33bbe8

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
import Definitions.Def_mme_recursive_yz_stage_certificate
import Mathlib.Tactic

section


/-!
# `a*b ≤ flatteningRank σ_0 (MMObj K a b c)` for `c ≥ 1`

The mode-0 flattening rank of the matrix-multiplication tensor `MM(a,b,c)` is at least
`a*b` whenever `c ≥ 1`. Direct-rank-functional proof: we construct `a*b` linearly
independent vectors in the range of the flattening map.

For each (i₀, j₀) ∈ Fin a × Fin b, take the left-block basis dual at `(i₀, j₀)`. Its
image under the flattening map equals `∑_k R_{i₀,j₀,k}`, where R is the right-block
pure tensor with mode-1 entry `e_{(j₀,k)}` and mode-2 entry `e_{(k,i₀)}`. These images
for different (i₀, j₀) have disjoint basis support (mode 1 starts with j₀, mode 2 ends
with i₀), so they're linearly independent when c ≥ 1. -/

set_option maxHeartbeats 1600000

universe u

open PiTensorProduct TensorProduct BigOperators Module

namespace MMEFlatteningRankMMObjAbSol

open MME

variable {K : Type u} [Field K]

section MMObj_ab

/-- The mode-0 split `{0} | {1,2}` of `Fin 3`. -/
private noncomputable abbrev σ0 : Split (Fin 3) := diagSplit (d := 3) (by norm_num)

/-- `σ0.S = {0}` has a unique element. -/
private instance σ0_S_subsingleton : Subsingleton (σ0 : Split (Fin 3)).S := by
  refine ⟨fun x y => ?_⟩
  ext
  have hx : (x : Fin 3) ∈ ({(0 : Fin 3)} : Finset (Fin 3)) := x.2
  have hy : (y : Fin 3) ∈ ({(0 : Fin 3)} : Finset (Fin 3)) := y.2
  rw [Finset.mem_singleton] at hx hy
  rw [hx, hy]

/-- The element `0 : Fin 3` packaged as a member of `σ0.S = {0}`. -/
private def sZero : (σ0 : Split (Fin 3)).S :=
  ⟨(0 : Fin 3), by simp [σ0, diagSplit]⟩

/-- `σ0.S` is nonempty. -/
private instance σ0_S_nonempty : Nonempty (σ0 : Split (Fin 3)).S := ⟨sZero⟩

/-- Decidable equality on `σ0.S`. -/
private instance σ0_S_decEq : DecidableEq (σ0 : Split (Fin 3)).S := by
  intro x y
  exact Decidable.isTrue (Subsingleton.elim _ _)

/-- The element `0 : Fin 3` is in `σ0.S`. -/
private lemma sZero_val : (sZero : (σ0 : Split (Fin 3)).S).val = 0 := rfl

/-- For any `s ∈ Sc σ0`, `s.val ≠ 0`. -/
private lemma sc_ne_zero (s : Sc (σ0 : Split (Fin 3))) : (s.val : Fin 3) ≠ 0 := by
  intro h
  have hm : (s.val : Fin 3) ∈ (σ0 : Split (Fin 3)).Sᶜ := s.2
  rw [h] at hm
  have h0 : (0 : Fin 3) ∈ (σ0 : Split (Fin 3)).S := by
    show (0 : Fin 3) ∈ ({(0 : Fin 3)} : Finset (Fin 3))
    rw [Finset.mem_singleton]
  exact Finset.mem_compl.mp hm h0

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

/-- The left-block family is constant `Fin a × Fin b → K`. -/
private lemma left_family_eq (a b c : ℕ) :
    (fun i : (σ0 : Split (Fin 3)).S => (MMObj K a b c).V i.val) =
    (fun _ : (σ0 : Split (Fin 3)).S => (Fin a × Fin b → K)) := by
  funext x
  have hx0 : (x : Fin 3) = 0 := Finset.mem_singleton.mp x.2
  rw [hx0]; rfl

/-- The right-block family equals `fun i => MMIdx a b c i.val → K`. -/
private lemma right_family_eq (a b c : ℕ) :
    (fun i : Sc (σ0 : Split (Fin 3)) => (MMObj K a b c).V i.val) =
    (fun i : Sc (σ0 : Split (Fin 3)) => (MMIdx a b c i.val → K)) := by
  funext x
  match h : (x.val : Fin 3) with
  | ⟨0, _⟩ => exact absurd h (sc_ne_zero x)
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl

/-- Per-mode basis (matching `MMSpace`). -/
private noncomputable def MMBasis (K : Type u) [Field K] (a b c : ℕ) :
    ∀ i : Fin 3, Basis (MMIdx a b c i) K (MMSpace K a b c i) := by
  intro i
  match i with
  | ⟨0, _⟩ => exact Pi.basisFun K (Fin a × Fin b)
  | ⟨1, _⟩ => exact Pi.basisFun K (Fin b × Fin c)
  | ⟨2, _⟩ => exact Pi.basisFun K (Fin c × Fin a)

/-- Left-block basis: indexed by `σ0.S → Fin a × Fin b`. -/
private noncomputable def bL (a b c : ℕ) :
    Basis ((σ0 : Split (Fin 3)).S → Fin a × Fin b) K
      (PiTensorProduct K (fun i : (σ0 : Split (Fin 3)).S =>
        (MMObj K a b c).V i.val)) :=
  Basis.piTensorProduct (fun i : (σ0 : Split (Fin 3)).S =>
    (show (MMIdx a b c i.val) = (Fin a × Fin b) by
      have hx0 : (i : Fin 3) = 0 := Finset.mem_singleton.mp i.2
      rw [hx0]; rfl) ▸ MMBasis K a b c i.val)

/-- Right-block basis: indexed by `∀ s : Sc σ0, MMIdx a b c s.val`. -/
private noncomputable def bR (a b c : ℕ) :
    Basis (∀ s : Sc (σ0 : Split (Fin 3)), MMIdx a b c s.val) K
      (PiTensorProduct K (fun i : Sc (σ0 : Split (Fin 3)) =>
        (MMObj K a b c).V i.val)) :=
  Basis.piTensorProduct (fun s : Sc (σ0 : Split (Fin 3)) => MMBasis K a b c s.val)

/-- The right-block basis index `g_{i₀,j₀,k}` corresponding to the pure tensor with
mode-1 entry `e_{(j₀,k)}` and mode-2 entry `e_{(k,i₀)}`. -/
private noncomputable def gR (a b c : ℕ)
    (i₀ : Fin a) (j₀ : Fin b) (k : Fin c) :
    ∀ s : Sc (σ0 : Split (Fin 3)), MMIdx a b c s.val := fun s =>
  match h : (s.val : Fin 3) with
  | ⟨0, _⟩ => absurd h (sc_ne_zero s)
  | ⟨1, _⟩ => (j₀, k)
  | ⟨2, _⟩ => (k, i₀)

/-- The candidate vector `vec (i₀, j₀)` in `V_right`: sum of right-block basis tensors
indexed by `gR i₀ j₀ k` for `k ∈ Fin c`. -/
private noncomputable def vec (a b c : ℕ) (ij : Fin a × Fin b) :
    PiTensorProduct K (fun i : Sc (σ0 : Split (Fin 3)) => (MMObj K a b c).V i.val) :=
  ∑ k : Fin c, bR a b c (gR a b c ij.1 ij.2 k)

/-- A concrete element of `Sc σ0` with value `1`. -/
private noncomputable def sOne : Sc (σ0 : Split (Fin 3)) :=
  ⟨(1 : Fin 3), by
    show (1 : Fin 3) ∈ (σ0 : Split (Fin 3)).Sᶜ
    rw [Finset.mem_compl]
    intro h
    have : (1 : Fin 3) ∈ ({(0 : Fin 3)} : Finset (Fin 3)) := h
    have h01 : (1 : Fin 3) = 0 := Finset.mem_singleton.mp this
    exact absurd h01 (by decide)⟩

/-- A concrete element of `Sc σ0` with value `2`. -/
private noncomputable def sTwo : Sc (σ0 : Split (Fin 3)) :=
  ⟨(2 : Fin 3), by
    show (2 : Fin 3) ∈ (σ0 : Split (Fin 3)).Sᶜ
    rw [Finset.mem_compl]
    intro h
    have : (2 : Fin 3) ∈ ({(0 : Fin 3)} : Finset (Fin 3)) := h
    have h02 : (2 : Fin 3) = 0 := Finset.mem_singleton.mp this
    exact absurd h02 (by decide)⟩

private lemma sOne_val : (sOne : Sc (σ0 : Split (Fin 3))).val = (1 : Fin 3) := rfl
private lemma sTwo_val : (sTwo : Sc (σ0 : Split (Fin 3))).val = (2 : Fin 3) := rfl

/-- `gR ij.1 ij.2 k` evaluated at `sOne` (mode-1 slot) gives `(ij.2, k)`. -/
private lemma gR_at_sOne (a b c : ℕ) (i₀ : Fin a) (j₀ : Fin b) (k : Fin c) :
    (gR a b c i₀ j₀ k sOne : MMIdx a b c (sOne : Sc (σ0 : Split (Fin 3))).val) = (j₀, k) := by
  unfold gR
  rfl

/-- `gR ij.1 ij.2 k` evaluated at `sTwo` (mode-2 slot) gives `(k, ij.1)`. -/
private lemma gR_at_sTwo (a b c : ℕ) (i₀ : Fin a) (j₀ : Fin b) (k : Fin c) :
    (gR a b c i₀ j₀ k sTwo : MMIdx a b c (sTwo : Sc (σ0 : Split (Fin 3))).val) = (k, i₀) := by
  unfold gR
  rfl

/-- The combined index `(ij, k) ↦ gR ij.1 ij.2 k` is injective. -/
private lemma gR_injective (a b c : ℕ) :
    Function.Injective (fun (p : (Fin a × Fin b) × Fin c) =>
      gR a b c p.1.1 p.1.2 p.2) := by
  rintro ⟨⟨i₀, j₀⟩, k⟩ ⟨⟨i₀', j₀'⟩, k'⟩ h
  simp only at h
  -- evaluate at sOne to get (j₀, k) = (j₀', k')
  have h1 : gR a b c i₀ j₀ k sOne = gR a b c i₀' j₀' k' sOne := by
    rw [h]
  rw [gR_at_sOne, gR_at_sOne] at h1
  -- evaluate at sTwo to get (k, i₀) = (k', i₀')
  have h2 : gR a b c i₀ j₀ k sTwo = gR a b c i₀' j₀' k' sTwo := by
    rw [h]
  rw [gR_at_sTwo, gR_at_sTwo] at h2
  obtain ⟨hj, hk⟩ := Prod.mk.inj h1
  obtain ⟨hk', hi⟩ := Prod.mk.inj h2
  simp [hi, hj, hk]

/-- For different `ij ≠ ij'`, the images `{gR ij.1 ij.2 k | k}` and
`{gR ij'.1 ij'.2 k | k}` are disjoint. -/
private lemma gR_disjoint (a b c : ℕ) {ij ij' : Fin a × Fin b} (hne : ij ≠ ij')
    (k k' : Fin c) :
    gR a b c ij.1 ij.2 k ≠ gR a b c ij'.1 ij'.2 k' := by
  intro h
  apply hne
  -- evaluate at sOne for j-component
  have h1 : gR a b c ij.1 ij.2 k sOne = gR a b c ij'.1 ij'.2 k' sOne := by rw [h]
  rw [gR_at_sOne, gR_at_sOne] at h1
  obtain ⟨hj, _⟩ := Prod.mk.inj h1
  -- evaluate at sTwo for i-component
  have h2 : gR a b c ij.1 ij.2 k sTwo = gR a b c ij'.1 ij'.2 k' sTwo := by rw [h]
  rw [gR_at_sTwo, gR_at_sTwo] at h2
  obtain ⟨_, hi⟩ := Prod.mk.inj h2
  exact Prod.ext hi hj

/-- **Linear independence of `vec`.** Uses dual functionals:
the basis coord `bR.coord (gR ij.1 ij.2 ⟨0, hc⟩)` evaluates to 1 on `vec ij` and to 0
on `vec ij'` for `ij ≠ ij'`. -/
private lemma vec_linearIndependent (a b c : ℕ) (hc : 1 ≤ c) :
    LinearIndependent K (vec (K := K) a b c) := by
  -- the dual functional family
  let φ : Fin a × Fin b → Dual K
      (PiTensorProduct K (fun i : Sc (σ0 : Split (Fin 3)) =>
        (MMObj K a b c).V i.val)) :=
    fun ij => (bR a b c).coord (gR a b c ij.1 ij.2 ⟨0, hc⟩)
  refine LinearIndependent.of_pairwise_dual_eq_zero_one (v := vec a b c) (f := φ) ?_ ?_
  · intro ij ij' hne
    -- φ ij (vec ij') = ∑_k bR.coord (gR ij.1 ij.2 ⟨0,hc⟩) (bR (gR ij'.1 ij'.2 k))
    -- = ∑_k δ_{gR ij'.1 ij'.2 k = gR ij.1 ij.2 ⟨0,hc⟩} = 0 (since ij' ≠ ij ⇒ disjoint)
    show φ ij (vec a b c ij') = 0
    unfold vec
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro k _
    rw [Basis.coord_apply, Basis.repr_self_apply]
    rw [if_neg]
    intro h
    exact gR_disjoint a b c (Ne.symm hne) k ⟨0, hc⟩ h
  · intro ij
    -- φ ij (vec ij) = ∑_k δ_{gR ij.1 ij.2 k = gR ij.1 ij.2 ⟨0,hc⟩} = 1 (only k=⟨0,hc⟩)
    show φ ij (vec a b c ij) = 1
    unfold vec
    rw [map_sum]
    rw [Finset.sum_eq_single (⟨0, hc⟩ : Fin c)]
    · rw [Basis.coord_apply, Basis.repr_self_apply, if_pos rfl]
    · intro k _ hk
      rw [Basis.coord_apply, Basis.repr_self_apply, if_neg]
      intro h
      have hinj := gR_injective a b c
      have : ((ij, k) : (Fin a × Fin b) × Fin c) = ((ij, ⟨0, hc⟩) : (Fin a × Fin b) × Fin c) := by
        apply hinj
        exact h
      have := (Prod.mk.inj this).2
      exact hk this
    · intro h; exact absurd (Finset.mem_univ _) h

/-! ### Step 2: Each `vec ij` is in the range of the flattening map. -/

/-- The dual functional that "picks out coordinate `ij`" via the singleton
identification of the left block. Concretely: pull back the evaluation-at-`ij`
functional on `Fin a × Fin b → K` through `subsingletonEquiv sZero`. -/
private noncomputable def dualL (a b c : ℕ) (ij : Fin a × Fin b) :
    Dual K (PiTensorProduct K (fun i : (σ0 : Split (Fin 3)).S =>
      (MMObj K a b c).V i.val)) :=
  (LinearMap.proj ij : (Fin a × Fin b → K) →ₗ[K] K).comp
    ((PiTensorProduct.subsingletonEquiv sZero).toLinearMap :
      PiTensorProduct K (fun i : (σ0 : Split (Fin 3)).S =>
        (MMObj K a b c).V i.val) →ₗ[K] (Fin a × Fin b → K))

/-- `dualL ij` applied to a pure tensor `tprod K v` evaluates `v 0` at `ij`. -/
private lemma dualL_tprod (a b c : ℕ) (ij : Fin a × Fin b)
    (v : ∀ s : (σ0 : Split (Fin 3)).S, (MMObj K a b c).V s.val) :
    dualL a b c ij (tprod K v) = (v sZero : Fin a × Fin b → K) ij := by
  unfold dualL
  rw [LinearMap.comp_apply, LinearMap.proj_apply]
  -- Use subsingletonEquiv_apply_tprod directly
  have h : (PiTensorProduct.subsingletonEquiv sZero : PiTensorProduct K
      (fun i : (σ0 : Split (Fin 3)).S => (MMObj K a b c).V i.val) ≃ₗ[K]
      (MMObj K a b c).V (sZero : (σ0 : Split (Fin 3)).S).val) (tprod K v) =
      v sZero :=
    PiTensorProduct.subsingletonEquiv_apply_tprod _ _
  -- coerce via toLinearMap
  show (PiTensorProduct.subsingletonEquiv sZero) (tprod K v) ij = v sZero ij
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

/-- The "left" tensor of the (i, j, k) term after `splitTensorEquiv σ0`. -/
private noncomputable def Lterm (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    PiTensorProduct K (fun s : (σ0 : Split (Fin 3)).S => (MMObj K a b c).V s.val) :=
  tprod K (fun s : (σ0 : Split (Fin 3)).S => modeData a b c i j k s.val)

/-- The "right" tensor of the (i, j, k) term after `splitTensorEquiv σ0`. -/
private noncomputable def Rterm (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    PiTensorProduct K (fun s : Sc (σ0 : Split (Fin 3)) => (MMObj K a b c).V s.val) :=
  tprod K (fun s : Sc (σ0 : Split (Fin 3)) => modeData a b c i j k s.val)

/-- `splitTensorEquiv` of one pure term decomposes into `Lterm ⊗ₜ Rterm`. -/
private lemma splitTensorEquiv_term (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    splitTensorEquiv σ0 (tprod K (modeData (K := K) a b c i j k))
      = Lterm a b c i j k ⊗ₜ[K] Rterm a b c i j k :=
  splitTensorEquiv_tprod _ _

/-- The `dualL ij` value on `Lterm i j k` is `δ_{(i,j) = ij}`. -/
private lemma dualL_Lterm (a b c : ℕ) (ij : Fin a × Fin b)
    (i : Fin a) (j : Fin b) (k : Fin c) :
    dualL a b c ij (Lterm a b c i j k) = if (i, j) = ij then (1 : K) else 0 := by
  unfold Lterm
  rw [dualL_tprod]
  -- modeData i j k (sZero : σ0.S).val = modeData i j k 0 = Pi.single (i, j) 1
  show (modeData (K := K) a b c i j k (sZero : (σ0 : Split (Fin 3)).S).val :
    Fin a × Fin b → K) ij = if (i, j) = ij then (1 : K) else 0
  -- by sZero_val: sZero.val = 0, so modeData ... 0 = Pi.single (i,j) 1
  rw [show modeData (K := K) a b c i j k (sZero : (σ0 : Split (Fin 3)).S).val =
      (Pi.single (i, j) 1 : Fin a × Fin b → K) from rfl]
  rw [Pi.single_apply]
  by_cases h : ij = (i, j)
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- `Rterm i j k = bR (gR i j k)`. -/
private lemma Rterm_eq_bR (a b c : ℕ) (i : Fin a) (j : Fin b) (k : Fin c) :
    (Rterm (K := K) a b c i j k) = bR (K := K) a b c (gR a b c i j k) := by
  unfold Rterm bR
  rw [Basis.piTensorProduct_apply]
  congr 1
  funext s
  show modeData (K := K) a b c i j k s.val = MMBasis K a b c s.val (gR a b c i j k s)
  -- Case analysis on s.val
  rcases s with ⟨sv, hsv⟩
  have hne : sv ≠ 0 := sc_ne_zero ⟨sv, hsv⟩
  match sv, hne with
  | ⟨1, hsv1⟩, _ =>
    show (Pi.single (j, k) 1 : Fin b × Fin c → K) =
      MMBasis K a b c (⟨1, hsv1⟩ : Fin 3) (gR a b c i j k ⟨⟨1, hsv1⟩, hsv⟩)
    show (Pi.single (j, k) 1 : Fin b × Fin c → K) =
      Pi.basisFun K (Fin b × Fin c) (gR a b c i j k ⟨⟨1, hsv1⟩, hsv⟩)
    rw [Pi.basisFun_apply]
    rfl
  | ⟨2, hsv2⟩, _ =>
    show (Pi.single (k, i) 1 : Fin c × Fin a → K) =
      MMBasis K a b c (⟨2, hsv2⟩ : Fin 3) (gR a b c i j k ⟨⟨2, hsv2⟩, hsv⟩)
    show (Pi.single (k, i) 1 : Fin c × Fin a → K) =
      Pi.basisFun K (Fin c × Fin a) (gR a b c i j k ⟨⟨2, hsv2⟩, hsv⟩)
    rw [Pi.basisFun_apply]
    rfl
  | ⟨0, _⟩, h => exact absurd rfl h

/-- The key formula expressing `flatteningMap σ0 (MMObj K a b c) (dualL ij)` as
`∑_{i,j,k} δ_{(i,j)=ij} • bR (gR i j k) = vec ij`. -/
private lemma flatteningMap_MMObj_dualL_eq_vec (a b c : ℕ) (ij : Fin a × Fin b) :
    flatteningMap σ0 (MMObj K a b c) (dualL a b c ij) = vec a b c ij := by
  -- Unfold flatteningMap.
  unfold flatteningMap
  -- Expand X.t.
  show tensorToDualHom K _ _ (splitTensorEquiv σ0 (MMTensor K a b c)) (dualL a b c ij) =
    vec a b c ij
  rw [MMTensor_eq_sum]
  -- distribute splitTensorEquiv through the triple sum
  rw [show splitTensorEquiv σ0 (∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        tprod K (modeData (K := K) a b c i j k))
      = ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        Lterm a b c i j k ⊗ₜ[K] Rterm a b c i j k from ?_]
  swap
  · simp only [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact splitTensorEquiv_term a b c i j k
  -- distribute tensorToDualHom through the sums.
  have hreduce : ((tensorToDualHom K
      (PiTensorProduct K (fun s : (σ0 : Split (Fin 3)).S => (MMObj K a b c).V s.val))
      (PiTensorProduct K (fun s : Sc (σ0 : Split (Fin 3)) => (MMObj K a b c).V s.val)))
      (∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        Lterm a b c i j k ⊗ₜ[K] Rterm a b c i j k)) (dualL a b c ij) =
      ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        dualL (K := K) a b c ij (Lterm a b c i j k) • Rterm (K := K) a b c i j k := by
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [tensorToDualHom_tmul]
  change ((tensorToDualHom K
      (PiTensorProduct K (fun s : (σ0 : Split (Fin 3)).S => (MMObj K a b c).V s.val))
      (PiTensorProduct K (fun s : Sc (σ0 : Split (Fin 3)) => (MMObj K a b c).V s.val)))
      (∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
        Lterm a b c i j k ⊗ₜ[K] Rterm a b c i j k)) (dualL a b c ij) = _
  rw [hreduce]
  -- now use dualL_Lterm to replace the dual value with δ
  simp_rw [dualL_Lterm]
  -- Replace Rterm with bR (gR i j k).
  simp_rw [Rterm_eq_bR]
  -- The goal now is:
  -- ∑ i, ∑ j, ∑ k, (if (i,j) = ij then 1 else 0) • bR (gR i j k) = vec ij
  -- vec ij = ∑_k bR (gR ij.1 ij.2 k).
  -- For each (i, j), the inner ∑_k is either 0 (if (i,j) ≠ ij) or ∑_k bR (gR i j k).
  -- Strategy: swap sums, then collapse i, j.
  unfold vec
  -- Goal: ∑ i, ∑ j, ∑ k, (if (i,j) = ij then 1 else 0) • bR (gR i j k) =
  --       ∑ k, bR (gR ij.1 ij.2 k)
  -- Collapse: for fixed k, ∑_{i,j} δ_{(i,j)=ij} bR (gR i j k) = bR (gR ij.1 ij.2 k).
  -- Then ∑_k ∑_{i,j} ... = ∑_k bR (...).
  -- Step: pull out the inner ∑_k, since the if condition doesn't depend on k.
  -- ∑_i ∑_j ∑_k (δ • bR) = ∑_i ∑_j (δ • ∑_k bR) = ∑_i ∑_j δ • (∑_k bR (gR i j k))
  -- Wait — the δ is independent of k, so we can move it outside ∑_k:
  -- ∑_i ∑_j ∑_k (δ • bR (gR i j k)) = ∑_i ∑_j (δ • ∑_k bR (gR i j k))
  simp_rw [← Finset.smul_sum]
  -- Goal: ∑ i, ∑ j, (if (i,j) = ij then 1 else 0) • ∑ k, bR (gR i j k) = ∑ k, bR (gR ij.1 ij.2 k)
  -- Now collapse ∑_i ∑_j δ • f(i,j) by Finset.sum_eq_single
  rw [Finset.sum_eq_single ij.1]
  · rw [Finset.sum_eq_single ij.2]
    · rw [if_pos rfl, one_smul]
    · intro j _ hj
      rw [if_neg, zero_smul]
      intro h
      apply hj
      exact (Prod.mk.inj h).2
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i _ hi
    rw [Finset.sum_eq_zero]
    intro j _
    rw [if_neg, zero_smul]
    intro h
    apply hi
    exact (Prod.mk.inj h).1
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **`vec ij ∈ range (flatteningMap σ0 (MMObj K a b c))`.** -/
private lemma vec_mem_range (a b c : ℕ) (ij : Fin a × Fin b) :
    vec a b c ij ∈ LinearMap.range (flatteningMap σ0 (MMObj K a b c)) := by
  exact ⟨dualL a b c ij, flatteningMap_MMObj_dualL_eq_vec a b c ij⟩

end MMObj_ab

end MMEFlatteningRankMMObjAbSol

/-! ### Main result (top-level for platform upload) -/

open MMEFlatteningRankMMObjAbSol MME

/-- The mode-0 flattening rank of `MMObj K a b c` is at least `a * b` when `c ≥ 1`.

Proof: we construct `a * b` linearly independent vectors `vec ij` in the range of the
flattening map. Each `vec ij = ∑_k bR (gR ij.1 ij.2 k)` is a sum of right-block basis
tensors, and the index map `(ij, k) ↦ gR ij.1 ij.2 k` is injective; combined with `c ≥ 1`,
this yields linear independence. The witness dual is `bL.coord (fun _ => ij)`. -/
theorem mme_flatteningRank_MMObj_ab {K : Type u} [Field K] (a b c : ℕ) (hc : 1 ≤ c) :
    a * b ≤ MME.flatteningRank (MME.diagSplit (d := 3) (by norm_num)) (MME.MMObj K a b c) := by
  -- The candidate vectors are `vec ij` for `ij ∈ Fin a × Fin b`.
  -- They are LI and contained in the range, so we get a*b ≤ finrank range.
  unfold flatteningRank
  -- Express vec via the range submodule.
  set V_right := PiTensorProduct K (fun i : Sc (σ0 : Split (Fin 3)) =>
    (MMObj K a b c).V i.val) with hVright
  haveI : FiniteDimensional K V_right :=
    Module.Finite.of_basis (bR a b c)
  set rangeFM := LinearMap.range (flatteningMap σ0 (MMObj K a b c)) with hrangeFM
  -- pull back vec into rangeFM
  let vecInRange : Fin a × Fin b → rangeFM := fun ij =>
    ⟨vec a b c ij, vec_mem_range a b c ij⟩
  -- LI of vecInRange follows from LI of vec.
  have hLI : LinearIndependent K vecInRange := by
    have hLI₀ : LinearIndependent K (vec (K := K) a b c) :=
      vec_linearIndependent a b c hc
    -- pulling back LI through subtype inclusion preserves LI
    exact hLI₀.of_comp rangeFM.subtype
  -- Apply: |Fin a × Fin b| ≤ finrank rangeFM.
  have hcard : Fintype.card (Fin a × Fin b) = a * b := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  -- finite-dim version
  have := hLI.fintype_card_le_finrank (R := K) (M := rangeFM)
  rw [hcard] at this
  exact this

end

section

open MME MME.TensorObj MME.HashExtraction MME.RecursiveYZ.Certificate Module
set_option autoImplicit false

namespace EmptyRecursiveAssembly

/-- No recursive factors, but a non-scalar requested matrix tensor. -/
def data : Data where
  factors := 0
  hash := fun j ↦ Fin.elim0 j
  repairCopies := 1
  repair_pos := by decide
  a := 2
  b := 2
  c := 2
  power := 0

def stages : ∀ j, Stage (data.hash j) := fun j ↦ Fin.elim0 j

lemma budgets : ∀ j, (stages j).Budget := fun j ↦ Fin.elim0 j

lemma unit_flattening_rank_le_one (σ : MME.Split (Fin 3)) :
    flatteningRank σ (oneObj : TensorObj ℚ 3) ≤ 1 := by
  classical
  let b := Basis.piTensorProduct
    (fun i : Sc σ ↦ Free.chooseBasis ℚ ((oneObj : TensorObj ℚ 3).V i))
  haveI := Module.Finite.of_basis b
  have hd : finrank ℚ (PiTensorProduct ℚ
      (fun i : Sc σ ↦ (oneObj : TensorObj ℚ 3).V i)) ≤ 1 := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_pi]
    apply Finset.prod_le_one (fun _ _ ↦ Nat.zero_le _)
    intro i _
    rw [← Module.finrank_eq_card_basis
      (Free.chooseBasis ℚ ((oneObj : TensorObj ℚ 3).V i))]
    change finrank ℚ ℚ ≤ 1
    simp
  exact (Submodule.finrank_le _).trans hd

lemma not_assembly : ¬ RecursiveAssembly data stages ℚ := by
  intro h
  have hr := h.2 (fun j ↦ Fin.elim0 j) (fun j ↦ Fin.elim0 j)
  have hrestrict : Restrict (MMObj ℚ 2 2 2) (oneObj : TensorObj ℚ 3) := by
    simpa [data, kronFin, bigAdd] using hr
  have hlow := mme_flatteningRank_MMObj_ab (K := ℚ) 2 2 2 (by decide)
  have hupp := hlow.trans ((flatteningRank_mono _ hrestrict).trans
    (unit_flattening_rank_le_one _))
  omega

/-- The stage budgets alone do not imply recursive assembly. -/
theorem finite_recursive_assembly_false :
    ¬ (∀ {K : Type} [Field K] (D : Data)
      (A : ∀ j, Stage (D.hash j)), (∀ j, (A j).Budget) → RecursiveAssembly D A K) := by
  intro h
  exact not_assembly (h (K := ℚ) data stages budgets)

end EmptyRecursiveAssembly


end

open MME MME.HashExtraction MME.RecursiveYZ.Certificate

theorem solution :
    ¬ (∀ {K : Type} [Field K] (D : Data)
      (A : ∀ j, Stage (D.hash j)), (∀ j, (A j).Budget) → RecursiveAssembly D A K) :=
  EmptyRecursiveAssembly.finite_recursive_assembly_false

#print axioms solution
