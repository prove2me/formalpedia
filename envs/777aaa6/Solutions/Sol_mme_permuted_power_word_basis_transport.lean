-- Prove2me | solution 1 for mme_permuted_power_word_basis_transport
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T05:01:19.903091+00:00
-- url     : https://prove2.me/submissions/fadb495b-f648-427f-8bae-6c7535f0fac2

import Definitions.Def_mme_permutation
import Definitions.Def_mme_kron_pow_mode_word_basis
import Definitions.Def_mme_TypeGrading_kron

open MME MME.DWZComponentRestriction Module TensorProduct PiTensorProduct
universe u
set_option autoImplicit false

private noncomputable def permutedPowerMap
    {K : Type u} [Field K] {X Y : TensorObj K 3}
    (e : Equiv.Perm (Fin 3))
    (f : ∀ i, (TensorObj.permObj e X).V i →ₗ[K] Y.V i) :
    (n : ℕ) → ∀ i,
      (TensorObj.permObj e (X.kronPow n)).V i →ₗ[K] (Y.kronPow n).V i
  | 0, _ => LinearMap.id
  | n + 1, i => TensorProduct.map (f i) (permutedPowerMap e f n i)

private theorem permutedPowerMap_tensor
    {K : Type u} [Field K] {X Y : TensorObj K 3}
    (e : Equiv.Perm (Fin 3))
    (f : ∀ i, (TensorObj.permObj e X).V i →ₗ[K] Y.V i)
    (hf : PiTensorProduct.map f (TensorObj.permObj e X).t = Y.t) :
    ∀ n, PiTensorProduct.map (permutedPowerMap e f n)
      (TensorObj.permObj e (X.kronPow n)).t = (Y.kronPow n).t
  | 0 => by
      change PiTensorProduct.map (fun _ => LinearMap.id)
        ((PiTensorProduct.reindex K (fun _ : Fin 3 => K) e)
          (PiTensorProduct.tprod K (fun _ => 1))) = _
      rw [PiTensorProduct.map_id, LinearMap.id_apply, PiTensorProduct.reindex_tprod]
      rfl
  | n + 1 => by
      change PiTensorProduct.map
        (fun i => TensorProduct.map (f i) (permutedPowerMap e f n i))
        ((PiTensorProduct.reindex K _ e) (interchange X.t (X.kronPow n).t)) = _
      rw [reindex_interchange, TensorObj.TypeGrading.kronMap_interchange]
      change interchange (PiTensorProduct.map f (TensorObj.permObj e X).t)
        (PiTensorProduct.map (permutedPowerMap e f n)
          (TensorObj.permObj e (X.kronPow n)).t) = _
      rw [hf, permutedPowerMap_tensor e f hf n]
      rfl

private theorem permutedPowerMap_basis
    {K : Type u} [Field K] {X Y : TensorObj K 3}
    (e : Equiv.Perm (Fin 3))
    (f : ∀ i, (TensorObj.permObj e X).V i →ₗ[K] Y.V i)
    (i : Fin 3) {ι : Type u}
    (b : Basis ι K (X.V (e.symm i))) (c : Basis ι K (Y.V i))
    (hb : ∀ a, f i (b a) = c a) :
    ∀ n (w : PowIndex ι n), permutedPowerMap e f n i
      (kronPowModeBasis X (e.symm i) b n w) = kronPowModeBasis Y i c n w
  | 0, w => by rfl
  | n + 1, w => by
      rcases w with ⟨a, w⟩
      change TensorProduct.map (f i) (permutedPowerMap e f n i)
        ((b.tensorProduct (kronPowModeBasis X (e.symm i) b n)) (a, w)) =
        (c.tensorProduct (kronPowModeBasis Y i c n)) (a, w)
      rw [Basis.tensorProduct_apply, TensorProduct.map_tmul, hb,
        permutedPowerMap_basis e f i b c hb n, Basis.tensorProduct_apply]

/-- A tensor map after a mode permutation lifts to all powers while preserving
the recursive word bases whenever its base maps preserve the chosen bases. -/
theorem solution
    {K : Type u} [Field K] {X Y : TensorObj K 3}
    (e : Equiv.Perm (Fin 3))
    (f : ∀ i, (TensorObj.permObj e X).V i →ₗ[K] Y.V i)
    (hf : PiTensorProduct.map f (TensorObj.permObj e X).t = Y.t)
    {ι : Fin 3 → Type u}
    (b : ∀ i, Basis (ι i) K (X.V (e.symm i)))
    (c : ∀ i, Basis (ι i) K (Y.V i))
    (hb : ∀ i a, f i (b i a) = c i a) (n : ℕ) :
    ∃ F : ∀ i, (TensorObj.permObj e (X.kronPow n)).V i →ₗ[K] (Y.kronPow n).V i,
      PiTensorProduct.map F (TensorObj.permObj e (X.kronPow n)).t =
        (Y.kronPow n).t ∧
      ∀ i (w : PowIndex (ι i) n),
        F i (kronPowModeBasis X (e.symm i) (b i) n w) =
          kronPowModeBasis Y i (c i) n w := by
  exact ⟨permutedPowerMap e f n, permutedPowerMap_tensor e f hf n,
    fun i => permutedPowerMap_basis e f i (b i) (c i) (hb i) n⟩

#print axioms solution
