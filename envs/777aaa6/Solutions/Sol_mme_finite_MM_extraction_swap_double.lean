-- Prove2me | solution 1 for mme_finite_MM_extraction_swap_double
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T12:34:35.361841+00:00
-- url     : https://prove2.me/submissions/440b2ae3-58d5-4713-b90c-023790404f4d

import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_mmobj_mul
import Theorems.Thm_mme_MMObj_permObj_swapFirstTwo

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} {k : ℕ}
    (a b c : Fin k → ℕ)
    (hrestrict : TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
      (cyclicSymmetrization T)) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun r : Fin (k * k) ↦
        let ij := finProdFinEquiv.symm r
        MMObj K
          (a ij.1 * c ij.2)
          (b ij.1 * b ij.2)
          (c ij.1 * a ij.2)))
      (sixSymmetrization T) := by
  let X := TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j))
  let C := cyclicSymmetrization T
  let P := TensorQ.tensorStrassen K 3 (by omega)
  have hXC : P.le (TensorQ.toQ X) (TensorQ.toQ C) := hrestrict
  have hswap : P.le
      (TensorQ.permAut swapFirstTwoPerm (TensorQ.toQ X))
      (TensorQ.permAut swapFirstTwoPerm (TensorQ.toQ C)) :=
    TensorQ.permAut_le swapFirstTwoPerm hXC
  have hleft : P.le
      (TensorQ.toQ X *
        TensorQ.permAut swapFirstTwoPerm (TensorQ.toQ X))
      (TensorQ.toQ C *
        TensorQ.permAut swapFirstTwoPerm (TensorQ.toQ X)) :=
    P.mul_right _ _ hXC _
  have hprod : P.le
      (TensorQ.toQ X *
        TensorQ.permAut swapFirstTwoPerm (TensorQ.toQ X))
      (TensorQ.toQ C *
        TensorQ.permAut swapFirstTwoPerm (TensorQ.toQ C)) :=
    P.le_trans _ _ _ hleft (by
      simpa only [mul_comm] using
        P.mul_right _ _ hswap (TensorQ.toQ C))
  rw [← TensorQ.le_toQ]
  have hsource :
      TensorQ.toQ
          (TensorObj.bigAdd (fun r : Fin (k * k) ↦
            let ij := finProdFinEquiv.symm r
            MMObj K
              (a ij.1 * c ij.2)
              (b ij.1 * b ij.2)
              (c ij.1 * a ij.2))) =
        TensorQ.toQ X *
          TensorQ.permAut swapFirstTwoPerm (TensorQ.toQ X) := by
    rw [TensorQ.toQ_bigAdd]
    calc
      (∑ r : Fin (k * k),
          TensorQ.toQ
            (MMObj K
              (a (finProdFinEquiv.symm r).1 *
                c (finProdFinEquiv.symm r).2)
              (b (finProdFinEquiv.symm r).1 *
                b (finProdFinEquiv.symm r).2)
              (c (finProdFinEquiv.symm r).1 *
                a (finProdFinEquiv.symm r).2))) =
          ∑ p : Fin k × Fin k,
            TensorQ.toQ
              (MMObj K (a p.1 * c p.2)
                (b p.1 * b p.2) (c p.1 * a p.2)) := by
        symm
        apply Fintype.sum_equiv finProdFinEquiv
        intro p
        simp
      _ = ∑ i : Fin k, ∑ j : Fin k,
          TensorQ.toQ (MMObj K (a i) (b i) (c i)) *
            TensorQ.permAut swapFirstTwoPerm
              (TensorQ.toQ (MMObj K (a j) (b j) (c j))) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [TensorQ.permAut_toQ]
        have hswapMM := mme_MMObj_permObj_swapFirstTwo
          (K := K) (a j) (b j) (c j)
        have hkron := MMObj_kron_iso (K := K)
          (a i) (b i) (c i) (c j) (b j) (a j)
        calc
          TensorQ.toQ
              (MMObj K (a i * c j) (b i * b j) (c i * a j)) =
              TensorQ.toQ
                (TensorObj.kron (MMObj K (a i) (b i) (c i))
                  (MMObj K (c j) (b j) (a j))) :=
            (TensorQ.toQ_eq_iff.mpr hkron).symm
          _ = TensorQ.toQ (MMObj K (a i) (b i) (c i)) *
              TensorQ.toQ (MMObj K (c j) (b j) (a j)) :=
            TensorQ.toQ_kron _ _
          _ = TensorQ.toQ (MMObj K (a i) (b i) (c i)) *
              TensorQ.toQ
                (TensorObj.permObj swapFirstTwoPerm
                  (MMObj K (a j) (b j) (c j))) := by
            rw [TensorQ.toQ_eq_iff.mpr hswapMM]
      _ = (∑ i : Fin k, TensorQ.toQ (MMObj K (a i) (b i) (c i))) *
          (∑ j : Fin k, TensorQ.permAut swapFirstTwoPerm
            (TensorQ.toQ (MMObj K (a j) (b j) (c j)))) := by
        symm
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
      _ = TensorQ.toQ X *
          TensorQ.permAut swapFirstTwoPerm (TensorQ.toQ X) := by
        dsimp only [X]
        rw [TensorQ.toQ_bigAdd, map_sum]
  have htarget :
      TensorQ.toQ (sixSymmetrization T) =
        TensorQ.toQ C *
          TensorQ.permAut swapFirstTwoPerm (TensorQ.toQ C) := by
    rw [sixSymmetrization, TensorQ.toQ_kron,
      ← TensorQ.permAut_toQ]
  rw [hsource, htarget]
  exact hprod
