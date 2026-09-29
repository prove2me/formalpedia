-- Prove2me | solution 1 for mme_dwz_central_022_202_power_word_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T05:37:16.717019+00:00
-- url     : https://prove2.me/submissions/20840fa9-a514-4a9f-a6a0-d7c7d3641df7

import Definitions.Def_mme_dwz_central_power_word_coordinates

open PiTensorProduct TensorProduct BigOperators
open MME
open MME.DWZFineChannel

universe u


set_option autoImplicit false
set_option linter.unusedSimpArgs false

private theorem littleEndianWordIndex_succ
    (P r : ℕ) (w : Fin (r + 1) → Fin P) :
    finProdFinEquiv
        (littleEndianWordIndex P r (fun i ↦ w i.succ), w 0) =
      littleEndianWordIndex P (r + 1) w := by
  apply Fin.ext
  simp [littleEndianWordIndex, finFunctionFinEquiv_apply,
    Fin.sum_univ_succ, pow_succ, finProdFinEquiv, Finset.mul_sum,
    mul_assoc, mul_comm, mul_left_comm]

private theorem fineChannelWordIndex_eq_littleEndian
    (q m : ℕ) (w : Fin m → Fine022Channel q) :
    fineChannelWordIndex q m w =
      littleEndianWordIndex (q ^ 2 + 2) m
        (fun i ↦ fine022ChannelEquiv q (w i)) := by
  rfl

private noncomputable def littleEndianMMWordVec
    (K : Type u) [Field K] (n m p : ℕ) :
    ∀ r : ℕ, (Fin r → Fin n) → (Fin r → Fin m) →
      (Fin r → Fin p) → ∀ s : Fin 3,
        ((MMObj K n m p).kronPow r).V s
  | 0, _, _, _, _ => (1 : K)
  | r + 1, wi, wj, wk, ⟨0, _⟩ =>
      (Pi.single (wi 0, wj 0) 1 : Fin n × Fin m → K) ⊗ₜ[K]
        littleEndianMMWordVec K n m p r
          (fun i ↦ wi i.succ) (fun i ↦ wj i.succ)
          (fun i ↦ wk i.succ) 0
  | r + 1, wi, wj, wk, ⟨1, _⟩ =>
      (Pi.single (wj 0, wk 0) 1 : Fin m × Fin p → K) ⊗ₜ[K]
        littleEndianMMWordVec K n m p r
          (fun i ↦ wi i.succ) (fun i ↦ wj i.succ)
          (fun i ↦ wk i.succ) 1
  | r + 1, wi, wj, wk, ⟨2, _⟩ =>
      (Pi.single (wk 0, wi 0) 1 : Fin p × Fin n → K) ⊗ₜ[K]
        littleEndianMMWordVec K n m p r
          (fun i ↦ wi i.succ) (fun i ↦ wj i.succ)
          (fun i ↦ wk i.succ) 2

private noncomputable def littleEndianMMFlatVec
    (K : Type u) [Field K] (n m p r : ℕ)
    (wi : Fin r → Fin n) (wj : Fin r → Fin m)
    (wk : Fin r → Fin p) :
    ∀ s : Fin 3, (MMObj K (n ^ r) (m ^ r) (p ^ r)).V s
  | ⟨0, _⟩ =>
      (Pi.single (littleEndianWordIndex n r wi,
          littleEndianWordIndex m r wj) 1 :
        Fin (n ^ r) × Fin (m ^ r) → K)
  | ⟨1, _⟩ =>
      (Pi.single (littleEndianWordIndex m r wj,
          littleEndianWordIndex p r wk) 1 :
        Fin (m ^ r) × Fin (p ^ r) → K)
  | ⟨2, _⟩ =>
      (Pi.single (littleEndianWordIndex p r wk,
          littleEndianWordIndex n r wi) 1 :
        Fin (p ^ r) × Fin (n ^ r) → K)

private theorem littleEndianPowerMaps_wordVec
    (K : Type u) [Field K] (n m p : ℕ) :
    ∀ (r : ℕ) (wi : Fin r → Fin n) (wj : Fin r → Fin m)
      (wk : Fin r → Fin p) (s : Fin 3),
      littleEndianPowerMaps K n m p r s
          (littleEndianMMWordVec K n m p r wi wj wk s) =
        littleEndianMMFlatVec K n m p r wi wj wk s := by
  intro r
  induction r with
  | zero =>
      intro wi wj wk s
      fin_cases s
      · change singletonPairMap K (1 : K) =
          (Pi.single (littleEndianWordIndex n 0 wi,
            littleEndianWordIndex m 0 wj) 1 :
            Fin (n ^ 0) × Fin (m ^ 0) → K)
        funext ab
        rw [show ab = (littleEndianWordIndex n 0 wi,
            littleEndianWordIndex m 0 wj) from Subsingleton.elim _ _]
        simp [singletonPairMap]
      · change singletonPairMap K (1 : K) =
          (Pi.single (littleEndianWordIndex m 0 wj,
            littleEndianWordIndex p 0 wk) 1 :
            Fin (m ^ 0) × Fin (p ^ 0) → K)
        funext ab
        rw [show ab = (littleEndianWordIndex m 0 wj,
            littleEndianWordIndex p 0 wk) from Subsingleton.elim _ _]
        simp [singletonPairMap]
      · change singletonPairMap K (1 : K) =
          (Pi.single (littleEndianWordIndex p 0 wk,
            littleEndianWordIndex n 0 wi) 1 :
            Fin (p ^ 0) × Fin (n ^ 0) → K)
        funext ab
        rw [show ab = (littleEndianWordIndex p 0 wk,
            littleEndianWordIndex n 0 wi) from Subsingleton.elim _ _]
        simp [singletonPairMap]
  | succ r ih =>
      intro wi wj wk s
      fin_cases s
      · simp only [littleEndianPowerMaps, littleEndianMMWordVec]
        change littleEndianKronEquiv K n m (n ^ r) (m ^ r)
            ((TensorProduct.map LinearMap.id
              (littleEndianPowerMaps K n m p r 0))
              ((Pi.single (wi 0, wj 0) 1 : Fin n × Fin m → K) ⊗ₜ[K]
                littleEndianMMWordVec K n m p r
                  (fun i ↦ wi i.succ) (fun i ↦ wj i.succ)
                  (fun i ↦ wk i.succ) 0)) = _
        rw [TensorProduct.map_tmul, LinearMap.id_apply, ih]
        change littleEndianKronEquiv K n m (n ^ r) (m ^ r)
            ((Pi.single (wi 0, wj 0) 1 : Fin n × Fin m → K) ⊗ₜ[K]
              (Pi.single
                (littleEndianWordIndex n r (fun i ↦ wi i.succ),
                  littleEndianWordIndex m r (fun i ↦ wj i.succ)) 1 :
                Fin (n ^ r) × Fin (m ^ r) → K)) =
          (Pi.single (littleEndianWordIndex n (r + 1) wi,
              littleEndianWordIndex m (r + 1) wj) 1 :
            Fin (n ^ (r + 1)) × Fin (m ^ (r + 1)) → K)
        rw [littleEndianKronEquiv_single,
          littleEndianWordIndex_succ, littleEndianWordIndex_succ]
        rfl
      · simp only [littleEndianPowerMaps, littleEndianMMWordVec]
        change littleEndianKronEquiv K m p (m ^ r) (p ^ r)
            ((TensorProduct.map LinearMap.id
              (littleEndianPowerMaps K n m p r 1))
              ((Pi.single (wj 0, wk 0) 1 : Fin m × Fin p → K) ⊗ₜ[K]
                littleEndianMMWordVec K n m p r
                  (fun i ↦ wi i.succ) (fun i ↦ wj i.succ)
                  (fun i ↦ wk i.succ) 1)) = _
        rw [TensorProduct.map_tmul, LinearMap.id_apply, ih]
        change littleEndianKronEquiv K m p (m ^ r) (p ^ r)
            ((Pi.single (wj 0, wk 0) 1 : Fin m × Fin p → K) ⊗ₜ[K]
              (Pi.single
                (littleEndianWordIndex m r (fun i ↦ wj i.succ),
                  littleEndianWordIndex p r (fun i ↦ wk i.succ)) 1 :
                Fin (m ^ r) × Fin (p ^ r) → K)) =
          (Pi.single (littleEndianWordIndex m (r + 1) wj,
              littleEndianWordIndex p (r + 1) wk) 1 :
            Fin (m ^ (r + 1)) × Fin (p ^ (r + 1)) → K)
        rw [littleEndianKronEquiv_single,
          littleEndianWordIndex_succ, littleEndianWordIndex_succ]
        rfl
      · simp only [littleEndianPowerMaps, littleEndianMMWordVec]
        change littleEndianKronEquiv K p n (p ^ r) (n ^ r)
            ((TensorProduct.map LinearMap.id
              (littleEndianPowerMaps K n m p r 2))
              ((Pi.single (wk 0, wi 0) 1 : Fin p × Fin n → K) ⊗ₜ[K]
                littleEndianMMWordVec K n m p r
                  (fun i ↦ wi i.succ) (fun i ↦ wj i.succ)
                  (fun i ↦ wk i.succ) 2)) = _
        rw [TensorProduct.map_tmul, LinearMap.id_apply, ih]
        change littleEndianKronEquiv K p n (p ^ r) (n ^ r)
            ((Pi.single (wk 0, wi 0) 1 : Fin p × Fin n → K) ⊗ₜ[K]
              (Pi.single
                (littleEndianWordIndex p r (fun i ↦ wk i.succ),
                  littleEndianWordIndex n r (fun i ↦ wi i.succ)) 1 :
                Fin (p ^ r) × Fin (n ^ r) → K)) =
          (Pi.single (littleEndianWordIndex p (r + 1) wk,
              littleEndianWordIndex n (r + 1) wi) 1 :
            Fin (p ^ (r + 1)) × Fin (n ^ (r + 1)) → K)
        rw [littleEndianKronEquiv_single,
          littleEndianWordIndex_succ, littleEndianWordIndex_succ]
        rfl

private theorem central022MMWordVec_eq_littleEndian
    (K : Type u) [Field K] (q : ℕ) :
    ∀ (m : ℕ) (w : Fin m → Fine022Channel q) (s : Fin 3),
      central022MMWordVec K q m w s =
        littleEndianMMWordVec K 1 1 (q ^ 2 + 2) m
          (fun _ ↦ 0) (fun _ ↦ 0)
          (fun i ↦ fine022ChannelEquiv q (w i)) s := by
  intro m
  induction m with
  | zero => intro w s; rfl
  | succ m ih =>
      intro w s
      fin_cases s <;>
        simp only [central022MMWordVec, littleEndianMMWordVec,
          fine022MMVec] <;>
        rw [ih] <;> rfl

private theorem central202MMWordVec_eq_littleEndian
    (K : Type u) [Field K] (q : ℕ) :
    ∀ (m : ℕ) (w : Fin m → Fine202Channel q) (s : Fin 3),
      central202MMWordVec K q m w s =
        littleEndianMMWordVec K (q ^ 2 + 2) 1 1 m
          (fun i ↦ fine202ChannelEquiv q (w i))
          (fun _ ↦ 0) (fun _ ↦ 0) s := by
  intro m
  induction m with
  | zero => intro w s; rfl
  | succ m ih =>
      intro w s
      fin_cases s <;>
        simp only [central202MMWordVec, littleEndianMMWordVec,
          fine202MMVec] <;>
        rw [ih] <;> rfl

theorem solution
    (K : Type u) [Field K] (q m : ℕ) :
    (∀ (w : Fin m → Fine022Channel q) (s : Fin 3),
      littleEndianPowerMaps K 1 1 (q ^ 2 + 2) m s
          (central022MMWordVec K q m w s) =
        central022FlatMMVec K q m (fineChannelWordIndex q m w) s) ∧
    (∀ (w : Fin m → Fine202Channel q) (s : Fin 3),
      littleEndianPowerMaps K (q ^ 2 + 2) 1 1 m s
          (central202MMWordVec K q m w s) =
        central202FlatMMVec K q m (fineChannelWordIndex q m w) s) := by
  constructor
  · intro w s
    rw [central022MMWordVec_eq_littleEndian,
      littleEndianPowerMaps_wordVec]
    fin_cases s <;>
      simp [littleEndianMMFlatVec, central022FlatMMVec,
        unitWordIndex, fineChannelWordIndex_eq_littleEndian,
        littleEndianWordIndex]
  · intro w s
    rw [central202MMWordVec_eq_littleEndian,
      littleEndianPowerMaps_wordVec]
    fin_cases s <;>
      simp [littleEndianMMFlatVec, central202FlatMMVec,
        unitWordIndex, fineChannelWordIndex_eq_littleEndian,
        littleEndianWordIndex,
        fine202ChannelEquiv]
