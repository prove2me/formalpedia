-- Prove2me | solution 1 for mme_degenerate_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-28T22:24:08.230018+00:00
-- url     : https://prove2.me/submissions/1e18cebf-a7e7-43ab-8c2b-c214eb9d87f2

import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Data.Nat.Lattice
import Definitions.Def_mme_degeneration
import Definitions.Def_mme_tensor_rank

/-! # Border rank bounds rank with polynomial overhead (Bini), `sorry`-free.

If `Z` degenerates from the diagonal unit `I_R` of order `H`, then truncating the
order-`H` degeneration at `ε^{H+1}` turns it into an honest restriction.  Concretely,
the degree-`H` coefficient `Φ.coeff H = Z.t` expands as a sum of pure tensors indexed by
`(antidiagonalTuple d H) × Fin R`, so `Z` is a restriction of the diagonal unit `I_N`
with `N = card(antidiagonalTuple d H) · R ≤ (H+1)^d · R`.  Hence
`tensorRankObj Z ≤ R · (H+1)^d`. -/

open MME PiTensorProduct BigOperators

universe u

namespace MME

variable {K : Type u} [Field K] {d : ℕ}

/-- If `Z.t` decomposes as a sum of `N` pure tensors, then `Z` is a restriction of the
diagonal unit tensor `I_N`. -/
private theorem restrict_diagObj_of_tprod_sum {Z : TensorObj K d} {N : ℕ}
    (w : Fin N → ∀ i, Z.V i) (hZ : Z.t = ∑ n : Fin N, tprod K (w n)) :
    TensorObj.Restrict Z (TensorObj.diagObj K d N) := by
  -- The restriction map: each mode `i` sends `Pi.single n 1 ↦ w n i`.
  refine ⟨fun i => ∑ n : Fin N,
    LinearMap.smulRight (LinearMap.proj n : (Fin N → K) →ₗ[K] K) (w n i), ?_⟩
  -- Evaluation of that map on a standard basis vector.
  have hf_eval : ∀ (i : Fin d) (k : Fin N),
      (∑ n : Fin N, LinearMap.smulRight (LinearMap.proj n : (Fin N → K) →ₗ[K] K) (w n i))
        (Pi.single k (1 : K)) = w k i := by
    intro i k
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply,
      LinearMap.proj_apply]
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
      (fun n _ hnk => by rw [Pi.single_eq_of_ne hnk, zero_smul])]
    simp
  -- Push `map f` through the diagonal tensor's defining sum.
  show PiTensorProduct.map _ (TensorObj.diagObj K d N).t = Z.t
  rw [hZ]
  show PiTensorProduct.map _
      (∑ n : Fin N, PiTensorProduct.tprod K (fun _ => (Pi.single n 1 : Fin N → K))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [PiTensorProduct.map_tprod]
  exact congrArg (PiTensorProduct.tprod K) (funext fun i => hf_eval i n)

/-- `card (antidiagonalTuple d k) ≤ (k+1)^d`. -/
private theorem card_antidiagonalTuple_le (d k : ℕ) :
    (Finset.Nat.antidiagonalTuple d k).card ≤ (k + 1) ^ d := by
  calc (Finset.Nat.antidiagonalTuple d k).card
      ≤ (Fintype.piFinset (fun _ : Fin d => Finset.range (k + 1))).card := by
        apply Finset.card_le_card
        intro j hj
        rw [Finset.Nat.mem_antidiagonalTuple] at hj
        simp only [Fintype.mem_piFinset, Finset.mem_range]
        intro i
        exact Nat.lt_succ_of_le
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i) |>.trans hj.le)
    _ = (k + 1) ^ d := by simp [Fintype.card_piFinset]

/-- **Border rank bounds rank with polynomial overhead (Bini).** -/
theorem solution {K : Type u} [Field K] {d : ℕ} {Z : TensorObj K d} {R H : ℕ}
    (hdeg : DegeneratesOfOrder Z (TensorObj.diagObj K d R) H) :
    tensorRankObj Z ≤ R * (H + 1) ^ d := by
  obtain ⟨Φ, _hvan, hcoeff⟩ := hdeg
  set S := Finset.Nat.antidiagonalTuple d H with hS
  -- Index type for the pure-tensor decomposition: tuples (in `S`) × the diagonal index.
  let ι := (↥S) × Fin R
  -- The pure tensor attached to index `(j, k)`.
  let w : ι → ∀ i, Z.V i :=
    fun p i => Φ.A i ((p.1 : Fin d → ℕ) i) (Pi.single p.2 (1 : K))
  -- `Z.t` is the sum of these pure tensors.
  have hZsum : Z.t = ∑ p : ι, PiTensorProduct.tprod K (w p) := by
    rw [← hcoeff]
    -- Expand `coeff H`.
    show (S.sum (fun j => PiTensorProduct.map (fun i => Φ.A i (j i))
            (TensorObj.diagObj K d R).t)) = _
    -- Per-tuple: `map` through the diagonal sum gives a sum of pure tensors.
    have hbody : ∀ j : Fin d → ℕ,
        PiTensorProduct.map (fun i => Φ.A i (j i)) (TensorObj.diagObj K d R).t
        = ∑ k : Fin R,
            PiTensorProduct.tprod K (fun i => Φ.A i (j i) (Pi.single k (1 : K))) := by
      intro j
      show PiTensorProduct.map (fun i => Φ.A i (j i))
          (∑ k : Fin R, PiTensorProduct.tprod K (fun _ => (Pi.single k 1 : Fin R → K))) = _
      rw [map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [PiTensorProduct.map_tprod]
    rw [Finset.sum_congr rfl (fun j _ => hbody j)]
    -- Convert `∑_{j ∈ S} ∑_{k}` to `∑_{p : S × Fin R}`.
    rw [← Finset.sum_coe_sort S
      (fun j => ∑ k : Fin R,
        PiTensorProduct.tprod K (fun i => Φ.A i (j i) (Pi.single k (1 : K))))]
    symm
    rw [Fintype.sum_prod_type]
  -- Bijection `ι ≃ Fin (Fintype.card ι)` reindexes onto the diagonal mode `Fin N`.
  set N := Fintype.card ι with hN
  let e : Fin N ≃ ι := (Fintype.equivFin ι).symm
  have hZsum' : Z.t = ∑ n : Fin N, tprod K (w (e n)) := by
    rw [hZsum]; exact (Equiv.sum_comp e (fun p => tprod K (w p))).symm
  -- `Z` restricts to `I_N`.
  have hres : TensorObj.Restrict Z (TensorObj.diagObj K d N) :=
    restrict_diagObj_of_tprod_sum (fun n => w (e n)) hZsum'
  -- `tensorRankObj Z ≤ N`.
  have hrank_le : tensorRankObj Z ≤ N := by
    apply Nat.sInf_le
    exact hres
  -- `N = card S · R ≤ (H+1)^d · R = R·(H+1)^d`.
  have hNeq : N = S.card * R := by
    rw [hN]; simp [ι, Fintype.card_prod, Fintype.card_coe]
  calc tensorRankObj Z ≤ N := hrank_le
    _ = S.card * R := hNeq
    _ ≤ (H + 1) ^ d * R := Nat.mul_le_mul_right R (card_antidiagonalTuple_le d H)
    _ = R * (H + 1) ^ d := Nat.mul_comm _ _

end MME

open MME in
/-- Top-level alias: the platform's prover looks for `solution`, not `MME.solution`. -/
theorem solution {K : Type u} [Field K] {d : ℕ} {Z : TensorObj K d} {R H : ℕ}
    (hdeg : DegeneratesOfOrder Z (TensorObj.diagObj K d R) H) :
    tensorRankObj Z ≤ R * (H + 1) ^ d :=
  MME.solution hdeg
