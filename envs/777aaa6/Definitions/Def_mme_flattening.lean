-- Prove2me | Definitions.Def_mme_flattening
-- name    : mme_flattening
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-29T15:35:12.964527+00:00
-- url     : https://prove2.me/theorems/a0a34288-33f2-492b-bc27-16678f2ca8a0
-- statement:
--   **Flattening rank and the diagonal order embedding for `TensorObj`.**
--
--   The combinatorial lower bound that forces $\mathrm{diagObj}\,n \leq \mathrm{diagObj}\,m \Rightarrow n \leq m$ — i.e., the `nat_order_embedding` axiom for the canonical Strassen preorder on the tensor quotient.
--
--   **Flattening.** Given a `Split` of the $d$ tensor modes into two non-empty blocks $S$ and $S^c$, a tensor object $X : \mathrm{TensorObj}\,K\,d$ is reindexed by `splitTensorEquiv` into an element of $(\bigotimes_{i \in S} V_i) \otimes (\bigotimes_{i \in S^c} V_i)$ — concretely, a matrix. The rank of that matrix is the **flattening rank** `flatteningRank σ X`.
--
--   **Properties.**
--   - `flatteningRank_mono`: flattening rank is *monotone under restriction* (`TensorObj.Restrict`).
--   - `flatteningRank_diag`: on the diagonal unit, `flatteningRank σ (diagObj K d r) = r`.
--
--   **The diagonal order embedding.** Combining the two: if $\mathrm{diagObj}\,n \leq \mathrm{diagObj}\,m$ (via $\mathrm{TensorObj}.\mathrm{Restrict}$), then $n = \mathrm{flatteningRank}\,\sigma\,(\mathrm{diagObj}\,n) \leq \mathrm{flatteningRank}\,\sigma\,(\mathrm{diagObj}\,m) = m$. This is the missing piece for the `nat_order_embedding` field of `tensorStrassen` on the tensor quotient.
--
--   **Implementation note.** Read-only port of `Prism/AsymptoticSpectra/Tensor/Flattening.lean`, adapted to MME's `TensorObj` (field names `acg/mod/fin`, restriction via `PiTensorProduct.map`, no `Fact (1 < d)` instance — split is built from a hypothesis `1 < d`).

import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Definitions.Def_mme_tensor
import Definitions.Def_mme_tensor_rank

/-! # Flattening rank and the diagonal order embedding

The flattening lower bound that forces `diagObj n ≤ diagObj m → n ≤ m`.

Given a `Split` of the `d` modes into two nonempty blocks `S` and `Sᶜ`, a tensor object
`X` can be reindexed (via `splitTensorEquiv`) into an element of
`(⨂_{i∈S} V i) ⊗ (⨂_{i∈Sᶜ} V i)`, i.e. a "matrix". The rank of that matrix —
`flatteningRank σ X` — cannot increase under restriction (`flatteningRank_mono`), and for
the diagonal tensor it equals `r` (`flatteningRank_diag`). Hence
`Restrict (diagObj n) (diagObj m) → n ≤ m`.

Ported (read-only) from `Prism/AsymptoticSpectra/Tensor/Flattening.lean`, adapted to MME's
`TensorObj` (field names `acg/mod/fin`, restriction via `PiTensorProduct.map`, no
`Fact (1 < d)` instance — the split is built from a hypothesis `1 < d`). -/

universe u v

open PiTensorProduct TensorProduct BigOperators Module

namespace MME

variable {K : Type u} [Field K] {d : ℕ}

/-- A two-block split of the index set: `S` and its complement are both nonempty. -/
structure Split (ι : Type*) [Fintype ι] [DecidableEq ι] where
  S : Finset ι
  hS : S.Nonempty
  hSc : Sᶜ.Nonempty

/-- Complement of the first block. -/
abbrev Sc (σ : Split (Fin d)) := σ.Sᶜ

/-- The two blocks of a split reassemble into the whole index set. -/
def splitEquiv (σ : Split (Fin d)) : σ.S ⊕ Sc σ ≃ Fin d where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun x := if h : x ∈ σ.S then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, Finset.mem_compl.mpr h⟩
  left_inv := fun
    | .inl ⟨x, hx⟩ => by simp only [Sum.elim_inl, hx, dif_pos]
    | .inr ⟨x, hx⟩ => by
        have hx' : x ∉ σ.S := Finset.mem_compl.mp hx
        simp only [Sum.elim_inr, hx', dif_neg, not_false_iff]
  right_inv x := by dsimp only; split_ifs with h <;> rfl

section SplitTensor

variable {V : Fin d → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- Reindex `⨂ᵢ Vᵢ` into the matrix shape `(⨂_{i∈S} Vᵢ) ⊗ (⨂_{i∈Sᶜ} Vᵢ)`. -/
noncomputable def splitTensorEquiv (σ : Split (Fin d)) :
    PiTensorProduct K V ≃ₗ[K]
      (PiTensorProduct K (fun i : σ.S => V i)) ⊗[K] (PiTensorProduct K (fun i : Sc σ => V i)) :=
  let step1 : PiTensorProduct K V ≃ₗ[K]
      PiTensorProduct K (fun i : σ.S ⊕ (Sc σ) => V (splitEquiv σ i)) :=
    PiTensorProduct.reindex K V (splitEquiv σ).symm
  let N : σ.S ⊕ (Sc σ) → Type u := fun i => V (splitEquiv σ i)
  let step2 : PiTensorProduct K N ≃ₗ[K]
      (PiTensorProduct K (fun i₁ : σ.S => N (.inl i₁))) ⊗[K]
      (PiTensorProduct K (fun i₂ : Sc σ => N (.inr i₂))) :=
    (PiTensorProduct.tmulEquivDep K N).symm
  step1.trans step2

/-- `splitTensorEquiv` on a pure tensor splits its factors along `S` and `Sᶜ`. -/
theorem splitTensorEquiv_tprod (σ : Split (Fin d)) (v : (i : Fin d) → V i) :
    splitTensorEquiv σ (tprod K v) =
      tprod K (fun (i : σ.S) => v i) ⊗ₜ[K] tprod K (fun (i : Sc σ) => v i) := by
  dsimp [splitTensorEquiv]
  erw [PiTensorProduct.reindex_tprod]
  simp only [Equiv.symm_symm]
  erw [PiTensorProduct.tmulEquivDep_symm_apply]
  congr

end SplitTensor

section Flattening

variable (K)

/-- The canonical "view a tensor as a matrix" map `A ⊗ B → (A* →ₗ B)`, sending
`a ⊗ b` to `f ↦ f(a) • b`. -/
noncomputable def tensorToDualHom (A B : Type*) [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] :
    A ⊗[K] B →ₗ[K] (Module.Dual K A →ₗ[K] B) :=
  TensorProduct.lift {
    toFun := fun a => {
      toFun := fun b => {
        toFun := fun f => f a • b
        map_add' := fun f g => add_smul (f a) (g a) b
        map_smul' := fun r f => by
          simp only [RingHom.id_apply, LinearMap.smul_apply]
          rw [smul_eq_mul, smul_smul] }
      map_add' := fun b₁ b₂ => by ext f; exact smul_add (f a) b₁ b₂
      map_smul' := fun r b => by ext f; exact smul_comm (f a) r b }
    map_add' := fun a₁ a₂ => by
      ext b f
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
      rw [map_add, add_smul]
    map_smul' := fun r a => by
      ext b f
      simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply,
        LinearMap.map_smul]
      rw [smul_eq_mul, smul_smul] }

@[simp]
theorem tensorToDualHom_tmul (A B : Type*) [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (a : A) (b : B) (f : Module.Dual K A) :
    tensorToDualHom K A B (a ⊗ₜ b) f = f a • b := by
  simp [tensorToDualHom]

variable {K}

/-- Naturality of `tensorToDualHom` under tensor-product maps (linear-map version). -/
theorem tensorToDualHom_map {A A' B B' : Type*}
    [AddCommGroup A] [Module K A] [AddCommGroup A'] [Module K A']
    [AddCommGroup B] [Module K B] [AddCommGroup B'] [Module K B']
    (fA : A →ₗ[K] A') (fB : B →ₗ[K] B') (t : A ⊗[K] B) (f : Module.Dual K A') :
    tensorToDualHom K A' B' (TensorProduct.map fA fB t) f =
    fB (tensorToDualHom K A B t (f ∘ₗ fA)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul a b =>
    simp only [TensorProduct.map_tmul, tensorToDualHom_tmul, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.map_smul]
  | add x y ihx ihy => simp only [map_add, LinearMap.add_apply, ihx, ihy]

/-- The flattening linear map of a tensor object along a split. -/
noncomputable def flatteningMap (σ : Split (Fin d)) (X : TensorObj K d) :
    Module.Dual K (PiTensorProduct K (fun i : σ.S => X.V i)) →ₗ[K]
    PiTensorProduct K (fun i : Sc σ => X.V i) :=
  tensorToDualHom K _ _ (splitTensorEquiv σ X.t)

/-- The flattening rank of a tensor object along a split. -/
noncomputable def flatteningRank (σ : Split (Fin d)) (X : TensorObj K d) : ℕ :=
  Module.finrank K (LinearMap.range (flatteningMap σ X))

/-- `splitTensorEquiv` commutes with `PiTensorProduct.map`: applying mode-wise linear maps
`f` then splitting equals splitting then tensoring the two block-restricted maps. -/
theorem splitTensorEquiv_map (σ : Split (Fin d))
    {V W : Fin d → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i) (t : PiTensorProduct K V) :
    splitTensorEquiv σ (PiTensorProduct.map f t) =
    TensorProduct.map
      (PiTensorProduct.map (fun (i : σ.S) => f i.val))
      (PiTensorProduct.map (fun (i : Sc σ) => f i.val))
      (splitTensorEquiv σ t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, PiTensorProduct.map_tprod]
    congr 1
    rw [splitTensorEquiv_tprod, splitTensorEquiv_tprod, TensorProduct.map_tmul,
      PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]
  | add x y ihx ihy => simp only [map_add, ihx, ihy]

/-- **Flattening rank is monotone under restriction.** A restriction `X ≤ Y` realises the
flattening of `X` as `fB ∘ (flattening of Y) ∘ fAᵀ`, whose range's dimension is at most
that of `flattening of Y`. -/
theorem flatteningRank_mono (σ : Split (Fin d)) {X Y : TensorObj K d}
    (h : TensorObj.Restrict X Y) : flatteningRank σ X ≤ flatteningRank σ Y := by
  obtain ⟨f, hf⟩ := h
  -- block-restricted maps
  set fA : PiTensorProduct K (fun i : σ.S => Y.V i) →ₗ[K]
      PiTensorProduct K (fun i : σ.S => X.V i) :=
    PiTensorProduct.map (fun (i : σ.S) => f i.val) with hfA
  set fB : PiTensorProduct K (fun i : Sc σ => Y.V i) →ₗ[K]
      PiTensorProduct K (fun i : Sc σ => X.V i) :=
    PiTensorProduct.map (fun (i : Sc σ) => f i.val) with hfB
  have split_eq : splitTensorEquiv σ X.t =
      TensorProduct.map fA fB (splitTensorEquiv σ Y.t) := by
    rw [← hf]; exact splitTensorEquiv_map σ f Y.t
  have flatteningMap_eq : flatteningMap σ X =
      fB.comp ((flatteningMap σ Y).comp fA.dualMap) := by
    ext g
    simp only [flatteningMap, LinearMap.comp_apply]
    rw [split_eq]
    exact tensorToDualHom_map fA fB (splitTensorEquiv σ Y.t) g
  unfold flatteningRank
  rw [flatteningMap_eq]
  -- finite-dimensionality of the two block tensor products
  haveI : ∀ i : Sc σ, Module.Finite K (X.V i) := fun i => inferInstance
  haveI : FiniteDimensional K (PiTensorProduct K (fun i : Sc σ => X.V i)) :=
    Module.Finite.of_basis (Basis.piTensorProduct (fun i => Module.Free.chooseBasis K (X.V i)))
  haveI : FiniteDimensional K (PiTensorProduct K (fun i : Sc σ => Y.V i)) :=
    Module.Finite.of_basis (Basis.piTensorProduct (fun i => Module.Free.chooseBasis K (Y.V i)))
  have h_range : LinearMap.range (fB.comp ((flatteningMap σ Y).comp fA.dualMap)) ≤
      Submodule.map fB (LinearMap.range (flatteningMap σ Y)) := by
    rintro x ⟨g, rfl⟩
    exact ⟨(flatteningMap σ Y) (fA.dualMap g), ⟨fA.dualMap g, rfl⟩, rfl⟩
  exact (Submodule.finrank_mono h_range).trans (Submodule.finrank_map_le fB _)

end Flattening

section Diagonal

/-- The split `S = {0}` of `Fin d` when `1 < d`. -/
noncomputable def diagSplit (hd : 1 < d) : Split (Fin d) :=
  have hd0 : 0 < d := by omega
  have : NeZero d := ⟨by omega⟩
  { S := {(0 : Fin d)}
    hS := Finset.singleton_nonempty _
    hSc := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      have hcard : ({(0 : Fin d)}ᶜ : Finset (Fin d)).card = 0 := by rw [h]; rfl
      rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin] at hcard
      omega }

/-- The block-`S` basis of `⨂_{i∈S} (diagObj K d r).V i` (each mode `= Fin r → K`),
indexed by `σ.S → Fin r`. Typed at `(diagObj).V` so it shares the codomain of
`flatteningMap σ (diagObj K d r)`. -/
private noncomputable def diagBasisS (σ : Split (Fin d)) (r : ℕ) :
    Basis (σ.S → Fin r) K (PiTensorProduct K (fun i : σ.S => (TensorObj.diagObj K d r).V i)) :=
  Basis.piTensorProduct (fun _ : σ.S => Pi.basisFun K (Fin r))

private noncomputable def diagBasisSc (σ : Split (Fin d)) (r : ℕ) :
    Basis (Sc σ → Fin r) K (PiTensorProduct K (fun i : Sc σ => (TensorObj.diagObj K d r).V i)) :=
  Basis.piTensorProduct (fun _ : Sc σ => Pi.basisFun K (Fin r))

/-- The diagonal flattens to the "identity matrix" `∑_j aⱼ ⊗ bⱼ`, where `aⱼ, bⱼ` are the
constant-`j` basis tensors of the two blocks. -/
private theorem splitTensorEquiv_diag (σ : Split (Fin d)) (r : ℕ) :
    splitTensorEquiv σ (TensorObj.diagObj K d r).t =
      ∑ j : Fin r, (diagBasisS σ r (fun _ => j)) ⊗ₜ[K] (diagBasisSc σ r (fun _ => j)) := by
  show splitTensorEquiv σ (∑ j : Fin r, tprod K (fun _ => (Pi.single j 1 : Fin r → K))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [splitTensorEquiv_tprod]
  congr 1
  · rw [diagBasisS, Basis.piTensorProduct_apply]
    congr 1; funext s; exact (Pi.basisFun_apply K (Fin r) j).symm
  · rw [diagBasisSc, Basis.piTensorProduct_apply]
    congr 1; funext s; exact (Pi.basisFun_apply K (Fin r) j).symm

/-- The flattening map of the diagonal sends a dual `f` to `∑_j f(aⱼ) • bⱼ`. -/
private theorem flatteningMap_diag (σ : Split (Fin d)) (r : ℕ)
    (f : Module.Dual K (PiTensorProduct K (fun i : σ.S => (TensorObj.diagObj K d r).V i))) :
    flatteningMap σ (TensorObj.diagObj K d r) f =
      ∑ j : Fin r, f (diagBasisS σ r (fun _ => j)) • (diagBasisSc σ r (fun _ => j)) := by
  have h1 : flatteningMap σ (TensorObj.diagObj K d r) f =
      (tensorToDualHom K _ _
        (∑ j : Fin r, (diagBasisS σ r (fun _ => j)) ⊗ₜ[K] (diagBasisSc σ r (fun _ => j)))) f := by
    unfold flatteningMap
    rw [splitTensorEquiv_diag]
  rw [h1, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [tensorToDualHom_tmul]

/-- **The diagonal's flattening rank equals `r`.** Its flattening is a rank-`r` "identity":
the range is the span of the `r` independent basis tensors `bⱼ`. -/
theorem flatteningRank_diag (σ : Split (Fin d)) (r : ℕ) :
    flatteningRank σ (TensorObj.diagObj K d r) = r := by
  unfold flatteningRank
  -- the `r` independent vectors bⱼ (typed at the flattening codomain `(diagObj).V`,
  -- which is defeq to `Fin r → K`)
  set b : Fin r → PiTensorProduct K (fun i : Sc σ => (TensorObj.diagObj K d r).V i) :=
    fun j => diagBasisSc σ r (fun _ => j) with hb
  -- index map j ↦ (fun _ => j) is injective since Sc σ is nonempty
  haveI : Nonempty (Sc σ) := σ.hSc.to_subtype
  have hinj : Function.Injective (fun (j : Fin r) (_ : Sc σ) => j) := by
    intro j k h
    have := congr_fun h (Classical.arbitrary (Sc σ))
    simpa using this
  have hli : LinearIndependent K b :=
    (diagBasisSc σ r).linearIndependent.comp _ hinj
  -- the range equals span of {bⱼ}
  have hrange : LinearMap.range (flatteningMap σ (TensorObj.diagObj K d r)) =
      Submodule.span K (Set.range b) := by
    apply le_antisymm
    · rintro x ⟨f, rfl⟩
      rw [flatteningMap_diag]
      apply Submodule.sum_mem
      intro j _
      exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨j, rfl⟩)
    · rw [Submodule.span_le]
      rintro x ⟨k, rfl⟩
      -- pick the dual functional that is 1 on a_k and 0 elsewhere
      refine ⟨(diagBasisS σ r).coord (fun _ => k), ?_⟩
      rw [flatteningMap_diag]
      rw [Finset.sum_eq_single k]
      · rw [Basis.coord_apply, Basis.repr_self_apply]
        simp [hb]
      · intro j _ hjk
        rw [Basis.coord_apply, Basis.repr_self_apply]
        have hne : (fun (_ : σ.S) => j) ≠ (fun _ => k) := by
          intro h
          haveI : Nonempty σ.S := σ.hS.to_subtype
          exact hjk (congr_fun h (Classical.arbitrary σ.S))
        rw [if_neg hne]
        simp
      · intro h; exact absurd (Finset.mem_univ k) h
  rw [hrange, finrank_span_eq_card hli, Fintype.card_fin]

end Diagonal

section OrderEmbedding

/-- **Easy direction.** `n ≤ m → diagObj n` restricts to `diagObj m`: the mode-wise map
`(Fin m → K) → (Fin n → K)`, precomposition with `Fin n ↪ Fin m`, sends each diagonal
pure tensor `e_jᵐ` to `e_kⁿ` (when `j = k`, `k < n`) or to `0` (when `j ≥ n`), so
`(diagObj m).t ↦ (diagObj n).t`. -/
theorem diag_le_restrict (hd : 0 < d) {n m : ℕ} (hnm : n ≤ m) :
    TensorObj.Restrict (TensorObj.diagObj K d n) (TensorObj.diagObj K d m) := by
  -- mode-wise restriction map: v ↦ (k ↦ v (castLE k))
  refine ⟨fun _ => LinearMap.funLeft K K (fun k : Fin n => Fin.castLE hnm k), ?_⟩
  show PiTensorProduct.map _ (∑ j : Fin m, tprod K (fun _ => (Pi.single j 1 : Fin m → K)))
      = ∑ k : Fin n, tprod K (fun _ => (Pi.single k 1 : Fin n → K))
  rw [map_sum]
  -- abbreviation for the image of `e_jᵐ` under the restriction map
  set L : (Fin m → K) →ₗ[K] (Fin n → K) :=
    LinearMap.funLeft K K (fun k : Fin n => Fin.castLE hnm k) with hL
  -- `map L` sends each diagonal pure tensor to `tprod (fun _ => L (e_jᵐ))`
  have hterm : ∀ j : Fin m,
      PiTensorProduct.map (fun _ : Fin d => L) (tprod K (fun _ => (Pi.single j 1 : Fin m → K)))
        = tprod K (fun _ : Fin d => L (Pi.single j 1 : Fin m → K)) := by
    intro j; rw [PiTensorProduct.map_tprod]
  simp only [hterm]
  -- terms outside the image of `Fin.castLE` vanish (their factor is `0`, and `d > 0`)
  have hd' : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hzero : ∀ j : Fin m, (¬ ∃ k : Fin n, Fin.castLE hnm k = j) →
      (tprod K (fun _ : Fin d => L (Pi.single j 1 : Fin m → K)) :
        PiTensorProduct K (fun _ : Fin d => (Fin n → K))) = 0 := by
    intro j hj
    have hLj : L (Pi.single j 1 : Fin m → K) = (0 : Fin n → K) := by
      ext l
      rw [hL, LinearMap.funLeft_apply, Pi.single_apply, if_neg (fun h => hj ⟨l, h⟩)]; rfl
    exact MultilinearMap.map_coord_zero (tprod K) (Classical.arbitrary (Fin d)) (by rw [hLj])
  -- reindex the surviving terms by `Fin.castLE`
  rw [show (∑ k : Fin n,
        tprod K (fun _ : Fin d => (Pi.single k 1 : Fin n → K)))
      = ∑ j ∈ Finset.univ.map (Fin.castLEEmb hnm),
        tprod K (fun _ : Fin d => L (Pi.single j 1 : Fin m → K)) from ?_]
  · refine (Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => hzero j ?_)).symm
    rintro ⟨k, rfl⟩
    exact hj (by simp [Fin.castLEEmb])
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    funext _
    -- `L (e_{castLE k}ᵐ) = e_kⁿ`
    ext l
    rw [hL, LinearMap.funLeft_apply, Pi.single_apply, Pi.single_apply]
    simp only [Fin.castLEEmb_apply, Fin.castLE_inj]

/-- **Hard direction (flattening lower bound).** If `diagObj n` restricts to `diagObj m`,
then `n ≤ m`: flattening rank cannot increase under restriction and equals the diagonal's
size, so `n = flatteningRank (diagObj n) ≤ flatteningRank (diagObj m) = m`. -/
theorem diag_restrict_le (hd : 1 < d) {n m : ℕ}
    (h : TensorObj.Restrict (TensorObj.diagObj K d n) (TensorObj.diagObj K d m)) :
    n ≤ m := by
  have key := flatteningRank_mono (diagSplit hd) h
  rwa [flatteningRank_diag, flatteningRank_diag] at key

/-- **The diagonal order embedding.** `diagObj n` restricts to `diagObj m` iff `n ≤ m`. -/
theorem diag_restrict_iff (hd : 1 < d) (n m : ℕ) :
    TensorObj.Restrict (TensorObj.diagObj K d n) (TensorObj.diagObj K d m) ↔ n ≤ m :=
  ⟨fun h => diag_restrict_le hd h, fun h => diag_le_restrict (by omega) h⟩

end OrderEmbedding

end MME


