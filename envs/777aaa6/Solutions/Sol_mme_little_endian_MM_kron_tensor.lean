-- Prove2me | solution 1 for mme_little_endian_MM_kron_tensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T04:47:40.142111+00:00
-- url     : https://prove2.me/submissions/7d05ef4c-6171-4e5b-939e-6db89c5dee1c

import Definitions.Def_mme_little_endian_MM_coordinate_router

open PiTensorProduct TensorProduct BigOperators
open MME
open MME.DWZFineChannel

universe u

set_option autoImplicit false

theorem solution
    (K : Type u) [Field K]
    (n m p n' m' p' : ℕ) :
    PiTensorProduct.map
        (fun s => (littleEndianModeEquiv K n m p n' m' p' s).toLinearMap)
        (TensorObj.kron (MMObj K n m p) (MMObj K n' m' p')).t =
      (MMObj K (n' * n) (m' * m) (p' * p)).t := by
  show PiTensorProduct.map
      (fun s => (littleEndianModeEquiv K n m p n' m' p' s).toLinearMap)
      (interchange (MMObj K n m p).t (MMObj K n' m' p').t) = _
  rw [littleEndianMMObj_t_eq, littleEndianMMObj_t_eq,
    littleEndianMMObj_t_eq]
  have hdist :
      interchange (K := K)
          (∑ i, ∑ j, ∑ k, littleEndianMMPure K n m p i j k)
          (∑ i', ∑ j', ∑ k', littleEndianMMPure K n' m' p' i' j' k') =
        ∑ i, ∑ j, ∑ k, ∑ i', ∑ j', ∑ k',
          interchange (K := K) (littleEndianMMPure K n m p i j k)
            (littleEndianMMPure K n' m' p' i' j' k') := by
    rw [LinearMap.map_sum₂]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_sum₂]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_sum₂]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [map_sum]
  refine (congrArg (PiTensorProduct.map
    (fun s => (littleEndianModeEquiv K n m p n' m' p' s).toLinearMap))
      hdist).trans ?_
  refine
    (show (PiTensorProduct.map
        (fun s => (littleEndianModeEquiv K n m p n' m' p' s).toLinearMap))
        (∑ i, ∑ j, ∑ k, ∑ i', ∑ j', ∑ k',
          interchange (K := K) (littleEndianMMPure K n m p i j k)
            (littleEndianMMPure K n' m' p' i' j' k')) =
      ∑ i, ∑ j, ∑ k, ∑ i', ∑ j', ∑ k',
        littleEndianMMPure K (n' * n) (m' * m) (p' * p)
          (finProdFinEquiv (i', i))
          (finProdFinEquiv (j', j))
          (finProdFinEquiv (k', k))
      from by
        refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
        refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
        refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
        refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun i' _ => ?_)
        refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun j' _ => ?_)
        refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun k' _ => ?_)
        exact littleEndianModeEquiv_pure K n m p n' m' p' i j k i' j' k').trans ?_
  have hgrouped :
      (∑ i : Fin n, ∑ j : Fin m, ∑ k : Fin p,
          ∑ i' : Fin n', ∑ j' : Fin m', ∑ k' : Fin p',
        littleEndianMMPure K (n' * n) (m' * m) (p' * p)
          (finProdFinEquiv (i', i))
          (finProdFinEquiv (j', j))
          (finProdFinEquiv (k', k))) =
      (∑ i : Fin n, ∑ i' : Fin n', ∑ j : Fin m,
          ∑ j' : Fin m', ∑ k : Fin p, ∑ k' : Fin p',
        littleEndianMMPure K (n' * n) (m' * m) (p' * p)
          (finProdFinEquiv (i', i))
          (finProdFinEquiv (j', j))
          (finProdFinEquiv (k', k))) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (∑ j : Fin m, ∑ k : Fin p, ∑ i' : Fin n',
          ∑ j' : Fin m', ∑ k' : Fin p',
        littleEndianMMPure K (n' * n) (m' * m) (p' * p)
          (finProdFinEquiv (i', i))
          (finProdFinEquiv (j', j))
          (finProdFinEquiv (k', k))) =
      (∑ j : Fin m, ∑ i' : Fin n', ∑ k : Fin p,
          ∑ j' : Fin m', ∑ k' : Fin p',
        littleEndianMMPure K (n' * n) (m' * m) (p' * p)
          (finProdFinEquiv (i', i))
          (finProdFinEquiv (j', j))
          (finProdFinEquiv (k', k)))
      from Finset.sum_congr rfl fun j _ => Finset.sum_comm]
    rw [Finset.sum_comm (γ := Fin n')]
    refine Finset.sum_congr rfl fun i' _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm (γ := Fin m')]
  rw [hgrouped]
  have hreversePairs :
      (∑ i : Fin n, ∑ i' : Fin n', ∑ j : Fin m,
          ∑ j' : Fin m', ∑ k : Fin p, ∑ k' : Fin p',
        littleEndianMMPure K (n' * n) (m' * m) (p' * p)
          (finProdFinEquiv (i', i))
          (finProdFinEquiv (j', j))
          (finProdFinEquiv (k', k))) =
      (∑ i' : Fin n', ∑ i : Fin n, ∑ j' : Fin m',
          ∑ j : Fin m, ∑ k' : Fin p', ∑ k : Fin p,
        littleEndianMMPure K (n' * n) (m' * m) (p' * p)
          (finProdFinEquiv (i', i))
          (finProdFinEquiv (j', j))
          (finProdFinEquiv (k', k))) := by
    rw [Finset.sum_comm (γ := Fin n')]
    refine Finset.sum_congr rfl fun i' _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm (γ := Fin m')]
    refine Finset.sum_congr rfl fun j' _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm (γ := Fin p')]
  rw [hreversePairs]
  rw [show (∑ I : Fin (n' * n), ∑ J : Fin (m' * m),
        ∑ Kk : Fin (p' * p),
      littleEndianMMPure K (n' * n) (m' * m) (p' * p) I J Kk) =
    ∑ ii' : Fin n' × Fin n, ∑ jj' : Fin m' × Fin m,
      ∑ kk' : Fin p' × Fin p,
      littleEndianMMPure K (n' * n) (m' * m) (p' * p)
        (finProdFinEquiv ii') (finProdFinEquiv jj') (finProdFinEquiv kk')
    from by
      rw [← finProdFinEquiv.sum_comp]
      refine Finset.sum_congr rfl fun _ _ => ?_
      rw [← finProdFinEquiv.sum_comp]
      refine Finset.sum_congr rfl fun _ _ => ?_
      rw [← finProdFinEquiv.sum_comp]]
  simp_rw [Fintype.sum_prod_type]
