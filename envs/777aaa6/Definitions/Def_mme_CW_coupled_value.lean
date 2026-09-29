-- Prove2me | Definitions.Def_mme_CW_coupled_value
-- name    : mme_CW_coupled_value
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-23T23:23:51.787289+00:00
-- url     : https://prove2.me/theorems/c0bcd201-6bbf-4fe8-91fe-301b635ca2c1
-- title:
--   Coupled Coppersmith--Winograd tensor-square constituent
-- statement:
--   **The coupled Coppersmith–Winograd constituent and the symmetric $\tau$-value.**
--
--   Fix a field $K$ and $q\in\mathbb{N}$. The *coupled constituent* $D_q$ is the four-sum trilinear form labelled $(d)$ in the tensor-square analysis of Coppersmith–Winograd (journal p. 266, restated in the lemma on p. 270). Its first two modes each carry two $q$-element coordinate families (written $x_{i,0}$ and $x_{0,k}$ with $1\le i,k\le q$, and likewise for $y$); its third mode carries two distinguished coordinates $z',z''$ and a $q\times q$ family $z_{i,k}$:
--
--   $$
--   D_q\;=\;\sum_{i=1}^{q}x_{i,0}\,y_{i,0}\,z'\;+\;\sum_{k=1}^{q}x_{0,k}\,y_{0,k}\,z''\;+\;\sum_{i,k=1}^{q}x_{i,0}\,y_{0,k}\,z_{i,k}\;+\;\sum_{i,k=1}^{q}x_{0,k}\,y_{i,0}\,z_{i,k}.
--   $$
--
--   This is the "nontrivial central block" whose value the coupled-weight improvement must estimate; the other constituents of the regrouped tensor square are plain matrix products.
--
--   The module also defines the *cyclic symmetrization* $A\otimes\pi(A)\otimes\pi^{2}(A)$, where $\pi$ cyclically permutes the three tensor modes, and declares that $A$ *has symmetric $\tau$-value at least* $V$ when this symmetrization has (unsymmetrized) $\tau$-value at least $V^{3}$ in the sense of `HasTauValueAtLeast`. This matches the symmetric value convention of Coppersmith–Winograd on journal p. 264: the value of a single tensor is the cube root of the value of the product of its three cyclic rotations.
--
--   **Formalization Note** The two $q$-families in modes 1–2 are encoded as `Fin q ⊕ Fin q` and the third mode as `Fin 2 ⊕ (Fin q × Fin q)`; the four monomial groups above are the literal support of `coupledTensor`. Provides `coupledObj K q : TensorObj K 3`, `cyclicSymmetrization`, and `HasSymmetricTauValueAtLeast`.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), coupled constituent (d) on journal p. 266 and the lemma on journal pp. 270--272; symmetric value on journal p. 264; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.PiTensorProduct
import Definitions.Def_mme_tau_value

/-!
# The coupled Coppersmith--Winograd constituent and symmetric value

The tensor below is the four-sum constituent labelled `(d)` on journal
p. 266 of Coppersmith--Winograd (1990), and stated again in the lemma on
p. 270.  Its first two modes each consist of two `q`-element coordinate
families.  Its third mode consists of two distinguished coordinates and one
`q × q` family.

The file also defines the cyclic symmetrization used in the paper's
definition of symmetric value on journal p. 264.
-/

universe u

open PiTensorProduct BigOperators

namespace MME

@[reducible] def CoupledSpace (K : Type u) (q : ℕ) : Fin 3 → Type u
  | ⟨0, _⟩ => (Fin q ⊕ Fin q) → K
  | ⟨1, _⟩ => (Fin q ⊕ Fin q) → K
  | ⟨2, _⟩ => (Fin 2 ⊕ (Fin q × Fin q)) → K

@[reducible] instance coupledSpaceAddCommGroup
    {K : Type u} [Field K] (q : ℕ) (i : Fin 3) :
    AddCommGroup (CoupledSpace K q i) :=
  match i with
  | ⟨0, _⟩ => Pi.addCommGroup
  | ⟨1, _⟩ => Pi.addCommGroup
  | ⟨2, _⟩ => Pi.addCommGroup

@[reducible] instance coupledSpaceModule
    {K : Type u} [Field K] (q : ℕ) (i : Fin 3) :
    Module K (CoupledSpace K q i) :=
  match i with
  | ⟨0, _⟩ => Pi.module _ _ _
  | ⟨1, _⟩ => Pi.module _ _ _
  | ⟨2, _⟩ => Pi.module _ _ _

instance coupledSpaceFinite
    {K : Type u} [Field K] (q : ℕ) (i : Fin 3) :
    Module.Finite K (CoupledSpace K q i) :=
  match i with
  | ⟨0, _⟩ => inferInstance
  | ⟨1, _⟩ => inferInstance
  | ⟨2, _⟩ => inferInstance

private noncomputable def coupledMonom
    (K : Type u) [Field K] (q : ℕ)
    (x y : Fin q ⊕ Fin q) (z : Fin 2 ⊕ (Fin q × Fin q)) :
    PiTensorProduct K (CoupledSpace K q) :=
  tprod K (fun s =>
    match s with
    | ⟨0, _⟩ => (Pi.single x 1 : (Fin q ⊕ Fin q) → K)
    | ⟨1, _⟩ => (Pi.single y 1 : (Fin q ⊕ Fin q) → K)
    | ⟨2, _⟩ => (Pi.single z 1 : (Fin 2 ⊕ (Fin q × Fin q)) → K))

/-- The four-sum constituent on CW90 journal pp. 266 and 270. -/
noncomputable def coupledTensor (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct K (CoupledSpace K q) :=
  (∑ i : Fin q,
      coupledMonom K q (Sum.inl i) (Sum.inl i) (Sum.inl 0)) +
  (∑ k : Fin q,
      coupledMonom K q (Sum.inr k) (Sum.inr k) (Sum.inl 1)) +
  (∑ i : Fin q, ∑ k : Fin q,
      coupledMonom K q (Sum.inl i) (Sum.inr k) (Sum.inr (i, k))) +
  (∑ i : Fin q, ∑ k : Fin q,
      coupledMonom K q (Sum.inr k) (Sum.inl i) (Sum.inr (i, k)))

/-- The coupled four-sum constituent packaged as an order-three tensor. -/
noncomputable def coupledObj (K : Type u) [Field K] (q : ℕ) :
    TensorObj K 3 where
  V := CoupledSpace K q
  t := coupledTensor K q

private def cycle3 : Equiv.Perm (Fin 3) where
  toFun i := ![1, 2, 0] i
  invFun i := ![2, 0, 1] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Relabel the three tensor modes by a permutation. -/
noncomputable def permuteModes
    {K : Type u} [Field K] (e : Equiv.Perm (Fin 3))
    (X : TensorObj K 3) : TensorObj K 3 where
  V i := X.V (e.symm i)
  t := PiTensorProduct.reindex K X.V e X.t

/-- `X ⊗ π(X) ⊗ π²(X)` for the cyclic mode permutation `π`, as in
the symmetric-value definition on CW90 journal p. 264. -/
noncomputable def cyclicSymmetrization
    {K : Type u} [Field K] (X : TensorObj K 3) : TensorObj K 3 :=
  TensorObj.kron X
    (TensorObj.kron (permuteModes cycle3 X)
      (permuteModes (cycle3.trans cycle3) X))

/-- `X` has symmetric tau-value at least `V` when its cyclic
symmetrization has (unsymmetrized) tau-value at least `V³`. -/
def HasSymmetricTauValueAtLeast
    {K : Type u} [Field K] (X : TensorObj K 3) (tau V : ℝ) : Prop :=
  HasTauValueAtLeast (cyclicSymmetrization X) tau (V ^ (3 : ℕ))

end MME


