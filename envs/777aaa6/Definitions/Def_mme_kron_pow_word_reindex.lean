-- Prove2me | Definitions.Def_mme_kron_pow_word_reindex
-- name    : mme_kron_pow_word_reindex
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T08:06:33.97588+00:00
-- url     : https://prove2.me/theorems/36c22c8b-6e04-4ee0-a9b9-fc2b9e6d8b11
-- title:
--   Position reindexing of recursive tensor-power words
-- statement:
--   Recursive words index the tensor-product basis of one mode of a tensor power. This definition identifies those recursive words with ordinary functions on the finite position set and lets every position permutation act by precomposition. The inverse permutation gives the inverse word reindexing, including for the empty tensor power.
--
--   This is the index-level action underlying the standard-form shuffling group: repeated component factors are permuted while the letter carried by each factor moves with it.
--
--   **Formalization Note** The reindexing convention is $(e\cdot w)(r)=w(e(r))$, matching the inverse-reindex action used for DWZ useful blocks after choosing the appropriate group-action orientation.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and Claims 5.8--5.9, PDF pp. 48--49 / printed pp. 47--48; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_kron_pow_mode_word_basis

/-!
# Reindexing recursive tensor-power words

The DWZ shuffling group permutes repeated component positions.  These
definitions realize that permutation on the recursive word indices used by
the canonical component-power bases.
-/

open MME

universe u

namespace MME.DWZComponentRestriction

set_option autoImplicit false
set_option warningAsError true

/-- Build a recursive tensor-power word from its ordinary finite function. -/
def PowIndex.ofFun {ι : Type u} : (n : ℕ) → (Fin n → ι) → PowIndex ι n
  | 0, _ => PUnit.unit
  | n + 1, f => (f 0, PowIndex.ofFun n (fun r => f r.succ))

@[simp] theorem PowIndex.get_ofFun {ι : Type u}
    (n : ℕ) (f : Fin n → ι) :
    PowIndex.get n (PowIndex.ofFun n f) = f := by
  induction n with
  | zero =>
      funext r
      exact r.elim0
  | succ n ih =>
      funext r
      refine Fin.cases ?_ (fun j => ?_) r
      · rfl
      · exact congrFun (ih (fun q => f q.succ)) j

@[simp] theorem PowIndex.ofFun_get {ι : Type u}
    (n : ℕ) (w : PowIndex ι n) :
    PowIndex.ofFun n (PowIndex.get n w) = w := by
  induction n with
  | zero =>
      cases w
      rfl
  | succ n ih =>
      rcases w with ⟨x, tail⟩
      change (x, PowIndex.ofFun n (PowIndex.get n tail)) = (x, tail)
      rw [ih]

/-- The equivalence between recursive words and ordinary finite words. -/
def PowIndex.equivFun (ι : Type u) (n : ℕ) :
    PowIndex ι n ≃ (Fin n → ι) where
  toFun := PowIndex.get n
  invFun := PowIndex.ofFun n
  left_inv := PowIndex.ofFun_get n
  right_inv := PowIndex.get_ofFun n

/-- Reindex a recursive word by a permutation of tensor-power positions. -/
def PowIndex.reindex {ι : Type u} {n : ℕ}
    (e : Equiv.Perm (Fin n)) (w : PowIndex ι n) : PowIndex ι n :=
  PowIndex.ofFun n (fun r => PowIndex.get n w (e r))

@[simp] theorem PowIndex.get_reindex {ι : Type u} {n : ℕ}
    (e : Equiv.Perm (Fin n)) (w : PowIndex ι n) :
    PowIndex.get n (PowIndex.reindex e w) =
      fun r => PowIndex.get n w (e r) := by
  exact PowIndex.get_ofFun n _

@[simp] theorem PowIndex.reindex_symm_reindex {ι : Type u} {n : ℕ}
    (e : Equiv.Perm (Fin n)) (w : PowIndex ι n) :
    PowIndex.reindex e.symm (PowIndex.reindex e w) = w := by
  apply (PowIndex.equivFun ι n).injective
  funext r
  simp [PowIndex.reindex]

end MME.DWZComponentRestriction


