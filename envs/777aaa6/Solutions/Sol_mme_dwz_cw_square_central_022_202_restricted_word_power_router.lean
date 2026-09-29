-- Prove2me | solution 1 for mme_dwz_cw_square_central_022_202_restricted_word_power_router
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T04:13:28.988378+00:00
-- url     : https://prove2.me/submissions/dfd9032a-06a0-447a-8699-14ecb577664a

import Definitions.Def_mme_dwz_cw_square_restricted_central_power_words
import Theorems.Thm_mme_dwz_cw_square_central_022_202_source_router

open PiTensorProduct TensorProduct
open MME
open MME.DWZFineChannel

universe u

set_option autoImplicit false

theorem solution
    (K : Type u) [Field K] (q m L G : ℕ) :
    (exists maps022 : ∀ s : Fin 3,
        ((Central022Block K q).kronPow m).V s →ₗ[K]
          ((MMObj K 1 1 (q ^ 2 + 2)).kronPow m).V s,
      PiTensorProduct.map maps022 ((Central022Block K q).kronPow m).t =
          ((MMObj K 1 1 (q ^ 2 + 2)).kronPow m).t ∧
      ∀ (w : CentralRestricted022Word q m L G) (s : Fin 3),
        maps022 s
            (central022SourceWordVec K q m
              (encodeCentralRestricted022Word w) s) =
          central022MMWordVec K q m
            (encodeCentralRestricted022Word w) s) ∧
    (exists maps202 : ∀ s : Fin 3,
        ((Central202Block K q).kronPow m).V s →ₗ[K]
          ((MMObj K (q ^ 2 + 2) 1 1).kronPow m).V s,
      PiTensorProduct.map maps202 ((Central202Block K q).kronPow m).t =
          ((MMObj K (q ^ 2 + 2) 1 1).kronPow m).t ∧
      ∀ (w : CentralRestricted022Word q m L G) (s : Fin 3),
        maps202 s
            (central202SourceWordVec K q m
              (encodeCentralRestricted022Word w) s) =
          central202MMWordVec K q m
            (encodeCentralRestricted022Word w) s) := by
  rcases mme_dwz_cw_square_central_022_202_source_router K q with
    ⟨⟨base022, hbase022, hletter022⟩,
      ⟨base202, hbase202, hletter202⟩⟩

  have htensor022 : ∀ n : ℕ,
      PiTensorProduct.map (central022PowerMapsFrom K q base022 n)
          ((Central022Block K q).kronPow n).t =
        ((MMObj K 1 1 (q ^ 2 + 2)).kronPow n).t := by
    intro n
    induction n with
    | zero =>
        change PiTensorProduct.map (fun _ : Fin 3 => LinearMap.id)
            (PiTensorProduct.tprod K (fun _ : Fin 3 => (1 : K))) =
          PiTensorProduct.tprod K (fun _ : Fin 3 => (1 : K))
        rw [PiTensorProduct.map_tprod]
        rfl
    | succ n ih =>
        change PiTensorProduct.map
            (fun s => TensorProduct.map (base022 s)
              (central022PowerMapsFrom K q base022 n s))
            (interchange
              ((cwSquareCanonicalGrading K q).blockTensor
                (cwSquareBlockType 0 2 2))
              ((Central022Block K q).kronPow n).t) =
          interchange (MMTensor K 1 1 (q ^ 2 + 2))
            ((MMObj K 1 1 (q ^ 2 + 2)).kronPow n).t
        rw [TensorObj.TypeGrading.kronMap_interchange, hbase022, ih]
        rfl

  have hword022 : ∀ (n : ℕ) (w : Fin n → Fine022Channel q)
      (s : Fin 3),
      central022PowerMapsFrom K q base022 n s
          (central022SourceWordVec K q n w s) =
        central022MMWordVec K q n w s := by
    intro n
    induction n with
    | zero =>
        intro w s
        rfl
    | succ n ih =>
        intro w s
        simp only [central022SourceWordVec, central022MMWordVec,
          central022PowerMapsFrom]
        calc
          _ = base022 s (central022SourceVec K q (w 0) s) ⊗ₜ[K]
                central022PowerMapsFrom K q base022 n s
                  (central022SourceWordVec K q n (fun r => w r.succ) s) :=
            TensorProduct.map_tmul (base022 s)
              (central022PowerMapsFrom K q base022 n s)
              (central022SourceVec K q (w 0) s)
              (central022SourceWordVec K q n (fun r => w r.succ) s)
          _ = _ := by
            rw [central022SourceVec, hletter022, ih]

  have htensor202 : ∀ n : ℕ,
      PiTensorProduct.map (central202PowerMapsFrom K q base202 n)
          ((Central202Block K q).kronPow n).t =
        ((MMObj K (q ^ 2 + 2) 1 1).kronPow n).t := by
    intro n
    induction n with
    | zero =>
        change PiTensorProduct.map (fun _ : Fin 3 => LinearMap.id)
            (PiTensorProduct.tprod K (fun _ : Fin 3 => (1 : K))) =
          PiTensorProduct.tprod K (fun _ : Fin 3 => (1 : K))
        rw [PiTensorProduct.map_tprod]
        rfl
    | succ n ih =>
        change PiTensorProduct.map
            (fun s => TensorProduct.map (base202 s)
              (central202PowerMapsFrom K q base202 n s))
            (interchange
              ((cwSquareCanonicalGrading K q).blockTensor
                (cwSquareBlockType 2 0 2))
              ((Central202Block K q).kronPow n).t) =
          interchange (MMTensor K (q ^ 2 + 2) 1 1)
            ((MMObj K (q ^ 2 + 2) 1 1).kronPow n).t
        rw [TensorObj.TypeGrading.kronMap_interchange, hbase202, ih]
        rfl

  have hword202 : ∀ (n : ℕ) (w : Fin n → Fine202Channel q)
      (s : Fin 3),
      central202PowerMapsFrom K q base202 n s
          (central202SourceWordVec K q n w s) =
        central202MMWordVec K q n w s := by
    intro n
    induction n with
    | zero =>
        intro w s
        rfl
    | succ n ih =>
        intro w s
        simp only [central202SourceWordVec, central202MMWordVec,
          central202PowerMapsFrom]
        calc
          _ = base202 s (central202SourceVec K q (w 0) s) ⊗ₜ[K]
                central202PowerMapsFrom K q base202 n s
                  (central202SourceWordVec K q n (fun r => w r.succ) s) :=
            TensorProduct.map_tmul (base202 s)
              (central202PowerMapsFrom K q base202 n s)
              (central202SourceVec K q (w 0) s)
              (central202SourceWordVec K q n (fun r => w r.succ) s)
          _ = _ := by
            rw [central202SourceVec, hletter202, ih]

  refine ⟨⟨central022PowerMapsFrom K q base022 m,
      htensor022 m, ?_⟩,
    ⟨central202PowerMapsFrom K q base202 m,
      htensor202 m, ?_⟩⟩
  · intro w s
    exact hword022 m (encodeCentralRestricted022Word w) s
  · intro w s
    exact hword202 m (encodeCentralRestricted022Word w) s
