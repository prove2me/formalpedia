-- Prove2me | solution 1 for mme_recursive_yz_stage_repair_nontrivial_of_MM_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T09:45:10.455657+00:00
-- url     : https://prove2.me/submissions/e0c2dbf4-5e2b-4126-9cc4-015fe432c3e0

import Definitions.Def_mme_tensor_bridge
import Definitions.Def_mme_recursive_yz_CW_cells
import Definitions.Def_mme_recursive_yz_stage_certificate

open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.Certificate MME.CompleteSplit
universe u v w

namespace RecursiveTemplateFeasibility

/-- Every zero tensor is a restriction of every source tensor. -/
theorem zero_restrict {K : Type*} [Field K] (X Y : TensorObj K 3)
    (hX : X.t = 0) : TensorObj.Restrict X Y := by
  refine ⟨fun _ => 0, ?_⟩
  have hz : PiTensorProduct.map (fun i => (0 : Y.V i →ₗ[K] X.V i)) =
      (0 : PiTensorProduct K Y.V →ₗ[K] PiTensorProduct K X.V) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod,
      LinearMap.zero_apply]
    exact MultilinearMap.map_coord_zero (PiTensorProduct.tprod K) 0 rfl
  rw [hz, LinearMap.zero_apply, hX]

theorem quotient_zero {K : Type*} [Field K] (X : TensorObj K 3)
    (hX : X.t = 0) : TensorQ.toQ X = 0 := by
  apply TensorQ.toQ_eq_iff.mpr
  exact ⟨zero_restrict X TensorObj.zeroObj hX,
    zero_restrict TensorObj.zeroObj X rfl⟩

theorem tensor_ne_zero_of_MM_restrict {K : Type u} [Field K]
    {X : TensorObj K 3} {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : TensorObj.Restrict (MMObj K a b c) X) : X.t ≠ 0 := by
  intro hz
  obtain ⟨f, hf⟩ := h
  rw [hz, map_zero] at hf
  exact MMq_ne_zero ha hb hc (quotient_zero _ hf.symm)

/-- An empty mode block annihilates the intact cell-profile tensor. -/
theorem unbroken_tensor_zero_of_block_empty
    {P : Type v} {C : Type w} [Fintype P]
    (K : Type u) [Field K] (q ell L : ℕ) (positions : Fin L ≃ P)
    (cell : P → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → CompleteWord ell → ℕ) (i : Fin 3)
    [IsEmpty (CWCells.Block ell cell shape mu i)] :
    (CWCells.unbroken K q ell L positions cell shape mu).t = 0 := by
  classical
  have hn (x : CWCells.WordIndex.{u} q ell L) :
      ¬ CWCells.allowed q ell L positions cell shape mu i x := by
    intro hx
    exact isEmptyElim (⟨CWCells.label q ell L positions x, hx⟩ :
      CWCells.Block ell cell shape mu i)
  have hv (z : (CWCells.unbroken K q ell L positions cell shape mu).V i) : z = 0 := by
    apply Subtype.ext
    have hz := z.property
    change z.val ∈ cwBasisGrade (CWCells.basis K q ell L i)
      (fun x => if CWCells.allowed q ell L positions cell shape mu i x then
        (0 : Fin 2) else 1) 0 at hz
    have hbot : z.val ∈ (⊥ : Submodule K ((CWCells.source K q ell L).V i)) := by
      simpa [cwBasisGrade, hn] using hz
    exact (Submodule.mem_bot K).mp hbot
  generalize (CWCells.unbroken K q ell L positions cell shape mu).t = t
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c f =>
    rw [MultilinearMap.map_coord_zero (PiTensorProduct.tprod K) i (hv (f i)), smul_zero]
  | add x y hx hy => simp [hx, hy]

/-- A nonzero extracted matrix tensor requires an inhabited profile block in every mode. -/
theorem blocks_nonempty_of_MM_restrict
    {P : Type v} {C : Type w} [Fintype P]
    (K : Type u) [Field K] (q ell L : ℕ) (positions : Fin L ≃ P)
    (cell : P → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → CompleteWord ell → ℕ)
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : TensorObj.Restrict (MMObj K a b c)
      (CWCells.unbroken K q ell L positions cell shape mu)) (i : Fin 3) :
    Nonempty (CWCells.Block ell cell shape mu i) := by
  classical
  by_contra hempty
  haveI : IsEmpty (CWCells.Block ell cell shape mu i) := not_nonempty_iff.mp hempty
  exact tensor_ne_zero_of_MM_restrict ha hb hc h
    (unbroken_tensor_zero_of_block_empty K q ell L positions cell shape mu i)

private theorem grade_of_cellWord
    {P C W G : Type*} [Fintype P]
    {cell : P → C} {grade : W → G} {shape : C → G} {mu : C → W → ℕ}
    (f : CellWord cell grade shape mu) (d : C) (w : W) (hw : 0 < mu d w) :
    grade w = shape d := by
  classical
  have hcount : 0 < count cell f.val d w := by
    rw [f.property.2 d w]
    exact hw
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcount
  have hp' : cell p = d ∧ f.val p = w := (Finset.mem_filter.mp hp).2
  simpa only [hp'.1, hp'.2] using f.property.1 p

/-- Positive profile entries must occur at the prescribed cell grade. -/
theorem profile_grade_of_MM_restrict
    {P : Type v} {C : Type w} [Fintype P]
    (K : Type u) [Field K] (q ell L : ℕ) (positions : Fin L ≃ P)
    (cell : P → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → CompleteWord ell → ℕ)
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : TensorObj.Restrict (MMObj K a b c)
      (CWCells.unbroken K q ell L positions cell shape mu))
    (i : Fin 3) (d : C) (w : CompleteWord ell) (hw : 0 < mu i d w) :
    CWCells.grade w = shape d i := by
  classical
  obtain ⟨f⟩ := blocks_nonempty_of_MM_restrict K q ell L positions cell shape mu ha hb hc h i
  exact grade_of_cellWord f d w hw

/-- A stage extracting a nonzero matrix tensor has a nontrivial repair exponent and scale. -/
theorem stage_repair_nontrivial_of_MM_restrict
    {K : Type u} [Field K] {D : HashExtraction.HashData} (A : Stage D)
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : TensorObj.Restrict (MMObj K a b c) (A.template K)) :
    0 < A.repairExponent ∧ 1 < A.repairScale := by
  have hpos (i : Fin 3) : 0 < Nat.card (CWCells.Block A.ell
      (fullCell A.total A.reference) (fun c i => (c.2.val i).val) A.mu i) := by
    haveI := blocks_nonempty_of_MM_restrict K 5 A.ell A.L A.positions
      (fullCell A.total A.reference) (fun c i => (c.2.val i).val) A.mu ha hb hc h i
    exact Nat.card_pos
  have hprod : 0 < ∏ i : Fin 3, Nat.card (CWCells.Block A.ell
      (fullCell A.total A.reference) (fun c i => (c.2.val i).val) A.mu i) :=
    Finset.prod_pos (fun i _ => hpos i)
  have hpow : 1 < A.repairScale ^ A.repairExponent := lt_of_le_of_lt hprod A.capacity
  constructor
  · by_contra hz
    have he : A.repairExponent = 0 := by omega
    simp [he] at hpow
  · by_contra hs
    have hs' : A.repairScale ≤ 1 := by omega
    have hp : A.repairScale ^ A.repairExponent ≤ 1 := by
      simpa using Nat.pow_le_pow_left hs' A.repairExponent
    omega

end RecursiveTemplateFeasibility

theorem solution
    {K : Type u} [Field K] {D : HashExtraction.HashData} (A : Stage D)
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : TensorObj.Restrict (MMObj K a b c) (A.template K)) :
    0 < A.repairExponent ∧ 1 < A.repairScale := by
  exact RecursiveTemplateFeasibility.stage_repair_nontrivial_of_MM_restrict A ha hb hc h
#print axioms solution
