-- Prove2me | Definitions.Def_mme_little_endian_MM_coordinate_router
-- name    : mme_little_endian_MM_coordinate_router
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T04:46:23.366472+00:00
-- url     : https://prove2.me/theorems/4087f57d-8c5b-49c1-af0c-666a267b6185
-- title:
--   Little-endian coordinate router for Kronecker products of MM tensors
-- statement:
--   For two matrix-multiplication tensors with dimensions $(n,m,p)$ and $(n^\\prime,m^\\prime,p^\\prime)$, this interface defines modewise linear equivalences from their Kronecker product to the matrix-multiplication coordinate spaces with dimensions\n\n$$\n(n^\\prime n,\\;m^\\prime m,\\;p^\\prime p).\n$$\n\nOn each pure matrix-multiplication term, all three indices are encoded in tail-before-head order. Consequently the coordinate convention agrees position by position with the little-endian base expansion of a literal tensor-power word.\n\nThis interface supports source-faithful laser-method zeroings in which a named channel word must survive under the MM tensor identification.\n\n**Formalization Note** The module records the standard MM pure tensors, the three mode equivalences, and their exact simultaneous basis action.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3 and Appendix A, https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_little_endian_kron_coordinate
import Definitions.Def_mme_tensor_rank

open PiTensorProduct TensorProduct BigOperators

namespace MME.DWZFineChannel

universe u

set_option autoImplicit false

noncomputable def littleEndianMMPure
    (K : Type u) [Field K] (n m p : ℕ)
    (i : Fin n) (j : Fin m) (k : Fin p) :
    PiTensorProduct K (MMSpace K n m p) :=
  tprod K (fun s : Fin 3 =>
    match s with
    | ⟨0, _⟩ =>
        (Pi.single (i, j) 1 : Fin n × Fin m → K)
    | ⟨1, _⟩ =>
        (Pi.single (j, k) 1 : Fin m × Fin p → K)
    | ⟨2, _⟩ =>
        (Pi.single (k, i) 1 : Fin p × Fin n → K))

theorem littleEndianMMObj_t_eq
    (K : Type u) [Field K] (n m p : ℕ) :
    (MMObj K n m p).t =
      ∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p,
        littleEndianMMPure K n m p i j k := rfl

private theorem littleEndianInterchange_tprod
    (K : Type u) [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V W : ι → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) =
      tprod K (fun i => v i ⊗ₜ[K] w i) := by
  show (interchange (tprod K v)) (tprod K w) = _
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  show (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

noncomputable def littleEndianModeEquiv
    (K : Type u) [Field K]
    (n m p n' m' p' : ℕ) : ∀ s : Fin 3,
    (TensorObj.kron (MMObj K n m p) (MMObj K n' m' p')).V s ≃ₗ[K]
      (MMObj K (n' * n) (m' * m) (p' * p)).V s
  | ⟨0, _⟩ => littleEndianKronEquiv K n m n' m'
  | ⟨1, _⟩ => littleEndianKronEquiv K m p m' p'
  | ⟨2, _⟩ => littleEndianKronEquiv K p n p' n'

theorem littleEndianModeEquiv_pure
    (K : Type u) [Field K]
    (n m p n' m' p' : ℕ)
    (i : Fin n) (j : Fin m) (k : Fin p)
    (i' : Fin n') (j' : Fin m') (k' : Fin p') :
    PiTensorProduct.map
        (fun s => (littleEndianModeEquiv K n m p n' m' p' s).toLinearMap)
        (interchange (littleEndianMMPure K n m p i j k)
          (littleEndianMMPure K n' m' p' i' j' k')) =
      littleEndianMMPure K (n' * n) (m' * m) (p' * p)
        (finProdFinEquiv (i', i))
        (finProdFinEquiv (j', j))
        (finProdFinEquiv (k', k)) := by
  have hint :
      interchange (littleEndianMMPure K n m p i j k)
          (littleEndianMMPure K n' m' p' i' j' k') =
        tprod K (fun s : Fin 3 =>
          (match s with
          | ⟨0, _⟩ =>
              (Pi.single (i, j) 1 : Fin n × Fin m → K)
          | ⟨1, _⟩ =>
              (Pi.single (j, k) 1 : Fin m × Fin p → K)
          | ⟨2, _⟩ =>
              (Pi.single (k, i) 1 : Fin p × Fin n → K) :
            MMSpace K n m p s) ⊗ₜ[K]
          (match s with
          | ⟨0, _⟩ =>
              (Pi.single (i', j') 1 : Fin n' × Fin m' → K)
          | ⟨1, _⟩ =>
              (Pi.single (j', k') 1 : Fin m' × Fin p' → K)
          | ⟨2, _⟩ =>
              (Pi.single (k', i') 1 : Fin p' × Fin n' → K) :
            MMSpace K n' m' p' s)) :=
    littleEndianInterchange_tprod K
      (V := MMSpace K n m p) (W := MMSpace K n' m' p')
      (fun s => match s with
      | ⟨0, _⟩ =>
          (Pi.single (i, j) 1 : Fin n × Fin m → K)
      | ⟨1, _⟩ =>
          (Pi.single (j, k) 1 : Fin m × Fin p → K)
      | ⟨2, _⟩ =>
          (Pi.single (k, i) 1 : Fin p × Fin n → K))
      (fun s => match s with
      | ⟨0, _⟩ =>
          (Pi.single (i', j') 1 : Fin n' × Fin m' → K)
      | ⟨1, _⟩ =>
          (Pi.single (j', k') 1 : Fin m' × Fin p' → K)
      | ⟨2, _⟩ =>
          (Pi.single (k', i') 1 : Fin p' × Fin n' → K))
  refine (congrArg (PiTensorProduct.map
    (fun s => (littleEndianModeEquiv K n m p n' m' p' s).toLinearMap))
      hint).trans ?_
  erw [PiTensorProduct.map_tprod]
  show PiTensorProduct.tprod K _ =
    littleEndianMMPure K (n' * n) (m' * m) (p' * p) _ _ _
  simp only [littleEndianMMPure]
  congr 1
  funext s
  fin_cases s
  · exact littleEndianKronEquiv_single K i j i' j'
  · exact littleEndianKronEquiv_single K j k j' k'
  · exact littleEndianKronEquiv_single K k i k' i'

end MME.DWZFineChannel


