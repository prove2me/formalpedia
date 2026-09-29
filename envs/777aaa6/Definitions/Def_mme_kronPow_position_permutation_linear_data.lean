-- Prove2me | Definitions.Def_mme_kronPow_position_permutation_linear_data
-- name    : mme_kronPow_position_permutation_linear_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T08:21:07.738983+00:00
-- url     : https://prove2.me/theorems/0bc87a00-d57a-4fe5-af9d-115df1a7bee3
-- title:
--   Explicit position-permutation linear data for tensor powers
-- statement:
--   Let $T$ be an order-$d$ tensor over a field $K$, and choose a basis $B_i$ in each mode. The recursively parenthesized mode space of $T^{\otimes n}$ has the corresponding word basis $B_i^{\otimes n}$, indexed by functions $w:\{0,\ldots,n-1\}\to B_i$. For every permutation $e\in S_n$, this package defines an explicit modewise linear equivalence $P_{e,i}$ by the rule
--
--   $$P_{e,i}(B_w)=B_{w\circ e}.$$
--
--   It also defines the factorwise power $f^{\otimes n}$ of a linear map $f$, providing the data needed to state natural commuting squares between position permutations and label-aligned block inclusions. This is the linear-algebra interface underlying the useful-block shuffle in the Hole Lemma.
--
--   **Formalization Note.** Words are indexed by `Fin n → ι`, while the ambient mode spaces retain the recursive parenthesization used by `TensorObj.kronPow`.
-- source:
--   Standard symmetric-monoidal reindexing of tensor powers, specialized to the standard-form shuffle in Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and Claim 5.9, PDF pp. 49--50 / printed pp. 48--49.

import Definitions.Def_mme_tensor
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Explicit position permutations on recursively represented tensor powers

These definitions expose the literal action on word-basis vectors.  In
particular, this is stronger data than a quotient-level tensor isomorphism.
-/

open MME PiTensorProduct TensorProduct Module

universe u

set_option autoImplicit false

namespace MME.TensorObj

variable {K : Type u} [Field K] {d : ℕ}

/-- The canonical word basis on one mode of a recursively represented tensor
power, indexed by ordinary functions on its positions. -/
noncomputable def kronPowModeWordBasis
    (T : TensorObj K d) (i : Fin d) {ι : Type u}
    (b : Basis ι K (T.V i)) :
    (n : ℕ) → Basis (Fin n → ι) K ((T.kronPow n).V i)
  | 0 => Basis.singleton (Fin 0 → ι) K
  | n + 1 => by
      letI : IsScalarTower K K (T.V i) :=
        IsScalarTower.of_algebraMap_smul (by simp)
      exact (Module.Basis.tensorProduct b
        (kronPowModeWordBasis T i b n)).reindex
          (Fin.consEquiv (fun _ : Fin (n + 1) ↦ ι))

/-- Reindex a word by precomposition with a position permutation. -/
def kronPowWordReindex {n : ℕ} (e : Equiv.Perm (Fin n)) (ι : Type u) :
    (Fin n → ι) ≃ (Fin n → ι) where
  toFun w := fun r ↦ w (e r)
  invFun w := fun r ↦ w (e.symm r)
  left_inv w := by
    funext r
    simp
  right_inv w := by
    funext r
    simp

/-- Reindex all mode words by the same position permutation. -/
def kronPowTensorWordReindex {n : ℕ} (e : Equiv.Perm (Fin n))
    (ι : Fin d → Type u) :
    (∀ i, Fin n → ι i) ≃ (∀ i, Fin n → ι i) :=
  Equiv.piCongrRight (fun i ↦ kronPowWordReindex e (ι i))

/-- The explicit linear equivalence on one mode of a tensor power which
permutes word-basis positions. -/
noncomputable def kronPowModePositionEquiv
    (T : TensorObj K d) (i : Fin d) {ι : Type u}
    (b : Basis ι K (T.V i)) (n : ℕ) (e : Equiv.Perm (Fin n)) :
    (T.kronPow n).V i ≃ₗ[K] (T.kronPow n).V i :=
  let B := kronPowModeWordBasis T i b n
  B.equiv B (kronPowWordReindex e ι)

/-- Apply one fixed mode map independently in every factor of a recursively
represented tensor power. -/
noncomputable def kronPowModeMap
    {T S : TensorObj K d} (i : Fin d)
    (f : T.V i →ₗ[K] S.V i) :
    (n : ℕ) → (T.kronPow n).V i →ₗ[K] (S.kronPow n).V i
  | 0 => LinearMap.id
  | n + 1 => TensorProduct.map f (kronPowModeMap i f n)

end MME.TensorObj


