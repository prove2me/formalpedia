-- Prove2me | solution 1 for mme_schonhage_pan_targetTensor_eq_Xobj_t
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:06:40.857563+00:00
-- url     : https://prove2.me/submissions/f35fdeab-aeda-4f83-979e-27ad434dc731

import Definitions.Def_mme_schonhage_pan_certificate

open MME PiTensorProduct BigOperators Finset Polynomial PanLeanBridge

universe u

set_option maxHeartbeats 12000000
set_option maxRecDepth 5000

variable {K : Type u} [Field K]

noncomputable section

private lemma mba (i : Fin 5) :
    modeBasis (K := K) 0 (.a i) = inc0 (K := K) 0
      (Pi.single ((0 : Fin 1), i) 1) := by
  unfold modeBasis inc0
  change (((Pi.basisFun K (Fin 1 × Fin 5)).prod
    ((Pi.basisFun K (Fin 11 × Fin 2)).prod
      (Pi.basisFun K (Fin 10 × Fin 11)))).reindex mode0Equiv) (.a i) = _
  rw [Module.Basis.reindex_apply]
  simp [mode0Equiv, Module.Basis.prod_apply, Pi.basisFun_apply]
  rfl

private lemma mbc (s : Fin 2) (k : Fin 11) (i : Fin 5) :
    modeBasis (K := K) 1 (.c s k i) = inc0 (K := K) 1
      (Pi.single (i, side11Equiv (s, k)) 1) := by
  unfold modeBasis inc0
  change (((Pi.basisFun K (Fin 5 × Fin 22)).prod
    ((Pi.basisFun K (Fin 2 × Fin 5)).prod
      (Pi.basisFun K (Fin 11 × Fin 1)))).reindex mode1Equiv) (.c s k i) = _
  rw [Module.Basis.reindex_apply]
  simp [mode1Equiv, Module.Basis.prod_apply, Pi.basisFun_apply]
  rfl

private lemma mbb (s : Fin 2) (k : Fin 11) :
    modeBasis (K := K) 2 (.b s k) = inc0 (K := K) 2
      (Pi.single (side11Equiv (s, k), (0 : Fin 1)) 1) := by
  unfold modeBasis inc0
  change (((Pi.basisFun K (Fin 22 × Fin 1)).prod
    ((Pi.basisFun K (Fin 5 × Fin 11)).prod
      (Pi.basisFun K (Fin 1 × Fin 10)))).reindex mode2Equiv) (.b s k) = _
  rw [Module.Basis.reindex_apply]
  simp [mode2Equiv, Module.Basis.prod_apply, Pi.basisFun_apply]
  rfl

private lemma mbu (s : Fin 2) (k : Fin 11) :
    modeBasis (K := K) 0 (.u s k) = inc1 (K := K) 0
      (Pi.single (k, s) 1) := by
  unfold modeBasis inc1
  change (((Pi.basisFun K (Fin 1 × Fin 5)).prod
    ((Pi.basisFun K (Fin 11 × Fin 2)).prod
      (Pi.basisFun K (Fin 10 × Fin 11)))).reindex mode0Equiv) (.u s k) = _
  rw [Module.Basis.reindex_apply]
  simp [mode0Equiv, Module.Basis.prod_apply, Pi.basisFun_apply,
    LinearMap.comp_apply]
  rfl

private lemma mbw (s : Fin 2) (i : Fin 5) :
    modeBasis (K := K) 1 (.w s i) = inc1 (K := K) 1
      (Pi.single (s, i) 1) := by
  unfold modeBasis inc1
  change (((Pi.basisFun K (Fin 5 × Fin 22)).prod
    ((Pi.basisFun K (Fin 2 × Fin 5)).prod
      (Pi.basisFun K (Fin 11 × Fin 1)))).reindex mode1Equiv) (.w s i) = _
  rw [Module.Basis.reindex_apply]
  simp [mode1Equiv, Module.Basis.prod_apply, Pi.basisFun_apply,
    LinearMap.comp_apply]
  rfl

private lemma mbv (k : Fin 11) (i : Fin 5) :
    modeBasis (K := K) 2 (.v k i) = inc1 (K := K) 2
      (Pi.single (i, k) 1) := by
  unfold modeBasis inc1
  change (((Pi.basisFun K (Fin 22 × Fin 1)).prod
    ((Pi.basisFun K (Fin 5 × Fin 11)).prod
      (Pi.basisFun K (Fin 1 × Fin 10)))).reindex mode2Equiv) (.v k i) = _
  rw [Module.Basis.reindex_apply]
  simp [mode2Equiv, Module.Basis.prod_apply, Pi.basisFun_apply,
    LinearMap.comp_apply]
  rfl

private lemma mbx (s : Fin 2) (k : Fin 11) (i : Fin 5) :
    modeBasis (K := K) 0 (.x s k i) = inc2 (K := K) 0
      (Pi.single (side5Equiv (s, i), k) 1) := by
  unfold modeBasis inc2
  change (((Pi.basisFun K (Fin 1 × Fin 5)).prod
    ((Pi.basisFun K (Fin 11 × Fin 2)).prod
      (Pi.basisFun K (Fin 10 × Fin 11)))).reindex mode0Equiv) (.x s k i) = _
  rw [Module.Basis.reindex_apply]
  simp [mode0Equiv, Module.Basis.prod_apply, Pi.basisFun_apply,
    LinearMap.comp_apply]
  rfl

private lemma mbz (k : Fin 11) :
    modeBasis (K := K) 1 (.z k) = inc2 (K := K) 1
      (Pi.single (k, (0 : Fin 1)) 1) := by
  unfold modeBasis inc2
  change (((Pi.basisFun K (Fin 5 × Fin 22)).prod
    ((Pi.basisFun K (Fin 2 × Fin 5)).prod
      (Pi.basisFun K (Fin 11 × Fin 1)))).reindex mode1Equiv) (.z k) = _
  rw [Module.Basis.reindex_apply]
  simp [mode1Equiv, Module.Basis.prod_apply, Pi.basisFun_apply,
    LinearMap.comp_apply]
  rfl

private lemma mby (s : Fin 2) (i : Fin 5) :
    modeBasis (K := K) 2 (.y s i) = inc2 (K := K) 2
      (Pi.single ((0 : Fin 1), side5Equiv (s, i)) 1) := by
  unfold modeBasis inc2
  change (((Pi.basisFun K (Fin 22 × Fin 1)).prod
    ((Pi.basisFun K (Fin 5 × Fin 11)).prod
      (Pi.basisFun K (Fin 1 × Fin 10)))).reindex mode2Equiv) (.y s i) = _
  rw [Module.Basis.reindex_apply]
  simp [mode2Equiv, Module.Basis.prod_apply, Pi.basisFun_apply,
    LinearMap.comp_apply]
  rfl

private lemma sum_side11_reindex {A : Type*} [AddCommMonoid A] (g : Fin 22 → A) :
    (∑ s : Fin 2, ∑ k : Fin 11, g (side11Equiv (s, k))) = ∑ x : Fin 22, g x := by
  calc
    _ = ∑ p : Fin 2 × Fin 11, g (side11Equiv p) :=
      (Fintype.sum_prod_type' (fun s k => g (side11Equiv (s, k)))).symm
    _ = _ := Equiv.sum_comp side11Equiv g

private lemma sum_side5_reindex {A : Type*} [AddCommMonoid A]
    (g : Fin 10 → Fin 11 → A) :
    (∑ s : Fin 2, ∑ i : Fin 5, ∑ k : Fin 11, g (side5Equiv (s, i)) k) =
      ∑ x : Fin 10, ∑ k : Fin 11, g x k := by
  calc
    _ = ∑ p : Fin 2 × Fin 5, ∑ k : Fin 11, g (side5Equiv p) k :=
      (Fintype.sum_prod_type'
        (fun s i => ∑ k : Fin 11, g (side5Equiv (s, i)) k)).symm
    _ = _ := Equiv.sum_comp side5Equiv (fun x => ∑ k : Fin 11, g x k)

private lemma sum_cycle_reindex {A : Type*} [AddCommMonoid A]
    (g : Fin 11 → Fin 2 → Fin 5 → A) :
    (∑ s : Fin 2, ∑ i : Fin 5, ∑ k : Fin 11, g k s i) =
      ∑ k : Fin 11, ∑ s : Fin 2, ∑ i : Fin 5, g k s i := by
  calc
    _ = ∑ s : Fin 2, ∑ k : Fin 11, ∑ i : Fin 5, g k s i := by
      apply Fintype.sum_congr
      intro s
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

private lemma MMObj_t_explicit (n m p : ℕ) : (MMObj K n m p).t =
    ∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p, tprod K (fun s : Fin 3 =>
      match s with
      | ⟨0, _⟩ => (Pi.single (i, j) 1 : Fin n × Fin m → K)
      | ⟨1, _⟩ => (Pi.single (j, k) 1 : Fin m × Fin p → K)
      | ⟨2, _⟩ => (Pi.single (k, i) 1 : Fin p × Fin n → K)) := rfl

private lemma pureABC_eq_map (s : Fin 2) (i : Fin 5) (k : Fin 11) :
    pureABC (K := K) s i k =
      PiTensorProduct.map (fun r => inc0 (K := K) r)
        (tprod K (fun r : Fin 3 => match r with
          | ⟨0, _⟩ => (Pi.single ((0 : Fin 1), i) 1 : Fin 1 × Fin 5 → K)
          | ⟨1, _⟩ =>
              (Pi.single (i, side11Equiv (s, k)) 1 : Fin 5 × Fin 22 → K)
          | ⟨2, _⟩ =>
              (Pi.single (side11Equiv (s, k), (0 : Fin 1)) 1 :
                Fin 22 × Fin 1 → K))) := by
  rw [PiTensorProduct.map_tprod]
  unfold pureABC
  congr 1
  funext r
  fin_cases r
  · exact mba i
  · exact mbc s k i
  · exact mbb s k

private lemma pureUWV_eq_map (s : Fin 2) (i : Fin 5) (k : Fin 11) :
    pureUWV (K := K) s i k =
      PiTensorProduct.map (fun r => inc1 (K := K) r)
        (tprod K (fun r : Fin 3 => match r with
          | ⟨0, _⟩ => (Pi.single (k, s) 1 : Fin 11 × Fin 2 → K)
          | ⟨1, _⟩ => (Pi.single (s, i) 1 : Fin 2 × Fin 5 → K)
          | ⟨2, _⟩ => (Pi.single (i, k) 1 : Fin 5 × Fin 11 → K))) := by
  rw [PiTensorProduct.map_tprod]
  unfold pureUWV
  congr 1
  funext r
  fin_cases r
  · exact mbu s k
  · exact mbw s i
  · exact mbv k i

private lemma pureXZY_eq_map (s : Fin 2) (i : Fin 5) (k : Fin 11) :
    pureXZY (K := K) s i k =
      PiTensorProduct.map (fun r => inc2 (K := K) r)
        (tprod K (fun r : Fin 3 => match r with
          | ⟨0, _⟩ =>
              (Pi.single (side5Equiv (s, i), k) 1 : Fin 10 × Fin 11 → K)
          | ⟨1, _⟩ => (Pi.single (k, (0 : Fin 1)) 1 : Fin 11 × Fin 1 → K)
          | ⟨2, _⟩ =>
              (Pi.single ((0 : Fin 1), side5Equiv (s, i)) 1 :
                Fin 1 × Fin 10 → K))) := by
  rw [PiTensorProduct.map_tprod]
  unfold pureXZY
  congr 1
  funext r
  fin_cases r
  · exact mbx s k i
  · exact mbz k
  · exact mby s i

private lemma sum_pureABC :
    (∑ s : Fin 2, ∑ i : Fin 5, ∑ k : Fin 11, pureABC (K := K) s i k) =
      PiTensorProduct.map (fun r => inc0 (K := K) r) (X0 (K := K)).t := by
  have hpure :
      (∑ s : Fin 2, ∑ i : Fin 5, ∑ k : Fin 11, pureABC (K := K) s i k) =
      ∑ s : Fin 2, ∑ i : Fin 5, ∑ k : Fin 11,
        PiTensorProduct.map (fun r => inc0 (K := K) r)
          (tprod K (fun r : Fin 3 => match r with
            | ⟨0, _⟩ => (Pi.single ((0 : Fin 1), i) 1 : Fin 1 × Fin 5 → K)
            | ⟨1, _⟩ =>
                (Pi.single (i, side11Equiv (s, k)) 1 : Fin 5 × Fin 22 → K)
            | ⟨2, _⟩ =>
                (Pi.single (side11Equiv (s, k), (0 : Fin 1)) 1 :
                  Fin 22 × Fin 1 → K))) := by
    apply Fintype.sum_congr
    intro s
    apply Fintype.sum_congr
    intro i
    apply Fintype.sum_congr
    intro k
    exact pureABC_eq_map s i k
  rw [hpure, MMObj_t_explicit]
  simp only [Fin.sum_univ_one, map_sum]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro i
  exact sum_side11_reindex
    (A := PiTensorProduct K (Xobj (K := K)).V)
    (fun x : Fin 22 =>
      PiTensorProduct.map (fun r => inc0 (K := K) r)
        (tprod K (fun r : Fin 3 => match r with
          | ⟨0, _⟩ => (Pi.single ((0 : Fin 1), i) 1 : Fin 1 × Fin 5 → K)
          | ⟨1, _⟩ => (Pi.single (i, x) 1 : Fin 5 × Fin 22 → K)
          | ⟨2, _⟩ => (Pi.single (x, (0 : Fin 1)) 1 : Fin 22 × Fin 1 → K))))

private lemma sum_pureUWV :
    (∑ s : Fin 2, ∑ i : Fin 5, ∑ k : Fin 11, pureUWV (K := K) s i k) =
      PiTensorProduct.map (fun r => inc1 (K := K) r) (X1 (K := K)).t := by
  have hpure :
      (∑ s : Fin 2, ∑ i : Fin 5, ∑ k : Fin 11, pureUWV (K := K) s i k) =
      ∑ s : Fin 2, ∑ i : Fin 5, ∑ k : Fin 11,
        PiTensorProduct.map (fun r => inc1 (K := K) r)
          (tprod K (fun r : Fin 3 => match r with
            | ⟨0, _⟩ => (Pi.single (k, s) 1 : Fin 11 × Fin 2 → K)
            | ⟨1, _⟩ => (Pi.single (s, i) 1 : Fin 2 × Fin 5 → K)
            | ⟨2, _⟩ => (Pi.single (i, k) 1 : Fin 5 × Fin 11 → K))) := by
    apply Fintype.sum_congr
    intro s
    apply Fintype.sum_congr
    intro i
    apply Fintype.sum_congr
    intro k
    exact pureUWV_eq_map s i k
  rw [hpure, MMObj_t_explicit]
  simp only [map_sum]
  exact sum_cycle_reindex _

private lemma sum_pureXZY :
    (∑ s : Fin 2, ∑ i : Fin 5, ∑ k : Fin 11, pureXZY (K := K) s i k) =
      PiTensorProduct.map (fun r => inc2 (K := K) r) (X2 (K := K)).t := by
  have hpure :
      (∑ s : Fin 2, ∑ i : Fin 5, ∑ k : Fin 11, pureXZY (K := K) s i k) =
      ∑ s : Fin 2, ∑ i : Fin 5, ∑ k : Fin 11,
        PiTensorProduct.map (fun r => inc2 (K := K) r)
          (tprod K (fun r : Fin 3 => match r with
            | ⟨0, _⟩ =>
                (Pi.single (side5Equiv (s, i), k) 1 : Fin 10 × Fin 11 → K)
            | ⟨1, _⟩ => (Pi.single (k, (0 : Fin 1)) 1 : Fin 11 × Fin 1 → K)
            | ⟨2, _⟩ =>
                (Pi.single ((0 : Fin 1), side5Equiv (s, i)) 1 :
                  Fin 1 × Fin 10 → K))) := by
    apply Fintype.sum_congr
    intro s
    apply Fintype.sum_congr
    intro i
    apply Fintype.sum_congr
    intro k
    exact pureXZY_eq_map s i k
  rw [hpure, MMObj_t_explicit]
  simp only [Fin.sum_univ_one, map_sum]
  exact sum_side5_reindex
    (A := PiTensorProduct K (Xobj (K := K)).V)
    (fun x : Fin 10 => fun k : Fin 11 =>
      PiTensorProduct.map (fun r => inc2 (K := K) r)
        (tprod K (fun r : Fin 3 => match r with
          | ⟨0, _⟩ => (Pi.single (x, k) 1 : Fin 10 × Fin 11 → K)
          | ⟨1, _⟩ => (Pi.single (k, (0 : Fin 1)) 1 : Fin 11 × Fin 1 → K)
          | ⟨2, _⟩ => (Pi.single ((0 : Fin 1), x) 1 : Fin 1 × Fin 10 → K))))

private lemma add3_t_decompose_generic {d : ℕ} (A B C : TensorObj K d) :
    (TensorObj.add A (TensorObj.add B C)).t =
      PiTensorProduct.map
        (fun r => LinearMap.inl K (A.V r) (B.V r × C.V r)) A.t +
      PiTensorProduct.map
        (fun r =>
          (LinearMap.inr K (A.V r) (B.V r × C.V r)).comp
            (LinearMap.inl K (B.V r) (C.V r))) B.t +
      PiTensorProduct.map
        (fun r =>
          (LinearMap.inr K (A.V r) (B.V r × C.V r)).comp
            (LinearMap.inr K (B.V r) (C.V r))) C.t := by
  change
    PiTensorProduct.map
        (fun r => LinearMap.inl K (A.V r) (B.V r × C.V r)) A.t +
      PiTensorProduct.map
        (fun r => LinearMap.inr K (A.V r) (B.V r × C.V r))
        (PiTensorProduct.map
            (fun r => LinearMap.inl K (B.V r) (C.V r)) B.t +
         PiTensorProduct.map
            (fun r => LinearMap.inr K (B.V r) (C.V r)) C.t) = _
  rw [map_add]
  simp only [PiTensorProduct.map_comp, LinearMap.comp_apply]
  abel

private lemma Xobj_t_decompose :
    (Xobj (K := K)).t =
      PiTensorProduct.map (fun r => inc0 (K := K) r) (X0 (K := K)).t +
      PiTensorProduct.map (fun r => inc1 (K := K) r) (X1 (K := K)).t +
      PiTensorProduct.map (fun r => inc2 (K := K) r) (X2 (K := K)).t := by
  change (TensorObj.add (X0 (K := K))
      (TensorObj.add (X1 (K := K)) (X2 (K := K)))).t = _
  simpa only [inc0, inc1, inc2] using
    add3_t_decompose_generic (K := K)
      (X0 (K := K)) (X1 (K := K)) (X2 (K := K))

theorem solution {K : Type u} [Field K] :
    PanLeanBridge.targetTensor (K := K) =
      (PanLeanBridge.Xobj (K := K)).t := by
  unfold PanLeanBridge.targetTensor
  simp only [Finset.sum_add_distrib]
  rw [sum_pureABC, sum_pureUWV, sum_pureXZY]
  exact Xobj_t_decompose.symm

end
