-- Prove2me | Definitions.Def_mme_multipart_block_split_data
-- name    : mme_multipart_block_split_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-23T05:56:51.288149+00:00
-- url     : https://prove2.me/theorems/fa054c08-a80d-4012-97b4-4fdabbb15c40
-- title:
--   Positions of a p-part block split by an arbitrary assignment
-- statement:
--   A split of a finite type of blocks into a given number of parts, by an arbitrary assignment of blocks to parts, lifted to fine positions. The count of a part is the number of blocks assigned to it and its size is that count times the number of letters per block; the split enumerates each part's blocks and lays a part's positions out block-major, so all the letters of a block stay together in the part its block was assigned to. Also two universe-polymorphic copies of the library's congruences for dependent sums and for products, which are needed because the parts are indexed by standard finite types while the blocks are an arbitrary type.
-- source:
--   Position bookkeeping for the regional constructions of Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, More Asymmetry Yields Faster Matrix Multiplication (https://arxiv.org/abs/2404.16349), sections 5-6, and of the Duan-Wu-Zhou fourth-power recursion (https://arxiv.org/abs/2210.10173), section 7. A generic combinatorial statement about splitting blocks into parts; no exponent claim.

import Mathlib

open BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u v w

namespace MME.MultiSplit

/-! ### Two universe-polymorphic congruences

`Equiv.sigmaCongrRight` and `Equiv.prodCongr` force their two type families into a single
universe, which is too rigid here: the parts are indexed by `Fin` types while the blocks form an
arbitrary type.  These two copies give each side its own universe. -/

/-- `Equiv.sigmaCongrRight` with the two fibre families in independent universes. -/
def sigmaCongrU {I : Type w} {F : I → Type u} {G : I → Type v} (e : ∀ i, F i ≃ G i) :
    ((i : I) × F i) ≃ ((i : I) × G i) where
  toFun z := ⟨z.1, e z.1 z.2⟩
  invFun z := ⟨z.1, (e z.1).symm z.2⟩
  left_inv := by rintro ⟨i, x⟩; simp
  right_inv := by rintro ⟨i, x⟩; simp

/-- `Equiv.prodCongr` on the left factor, with the two factors in independent universes. -/
def prodCongrU {A : Type u} {C : Type v} (D : Type w) (e : A ≃ C) : A × D ≃ C × D where
  toFun z := (e z.1, z.2)
  invFun z := ((e.symm z.1), z.2)
  left_inv := by rintro ⟨x, y⟩; simp
  right_inv := by rintro ⟨x, y⟩; simp

/-! ### The `p`-part block split

`B` is a finite type of blocks, `part : B → Fin p` assigns each block to one of `p` parts, and
each block owns `len` fine positions inside the part it is assigned to.  Nothing is assumed about
the assignment: a part may be empty, and the blocks it draws need not be contiguous in any
enumeration of `B`. -/

variable {p : ℕ} {B : Type u} [Fintype B]

/-- The number of blocks the assignment gives to part `j`. -/
def multiCount (part : B → Fin p) (j : Fin p) : ℕ := Fintype.card {b : B // part b = j}

/-- The number of fine positions of part `j`, at `len` letters per block. -/
def multiSize (len : ℕ) (part : B → Fin p) (j : Fin p) : ℕ := len * multiCount part j

/-- A part's positions are its blocks times its letters. -/
theorem multiLen (len : ℕ) (part : B → Fin p) (j : Fin p) :
    multiCount part j * len = multiSize len part j := Nat.mul_comm _ _

/-- An enumeration of the blocks of part `j`. -/
noncomputable def multiEnum (part : B → Fin p) (j : Fin p) :
    {b : B // part b = j} ≃ Fin (multiCount part j) := Fintype.equivFin _

/-- The blocks of the parts, listed part by part, are exactly the blocks. -/
noncomputable def multiBlocks (part : B → Fin p) :
    ((j : Fin p) × Fin (multiCount part j)) ≃ B :=
  (sigmaCongrU fun j ↦ (multiEnum part j).symm).trans (Equiv.sigmaFiberEquiv part)

/-- The index of a block inside its own part. -/
noncomputable def multiIdx (part : B → Fin p) (b : B) : Fin (multiCount part (part b)) :=
  multiEnum part (part b) ⟨b, rfl⟩

/-- Inside part `j`, the positions are its blocks times `len` letters, block-major. -/
noncomputable def multiSplitPos (len : ℕ) (part : B → Fin p) (j : Fin p) :
    Fin (multiSize len part j) ≃ Fin (multiCount part j) × Fin len :=
  (finCongr (multiLen len part j).symm).trans finProdFinEquiv.symm

/-- The positions of the `p`-part block split.  Part `j` owns `len` positions for each of the
blocks assigned to it, and all `len` letters of a block stay inside one part. -/
noncomputable def multiPositions {N : ℕ} (len : ℕ) (part : B → Fin p)
    (pos : B × Fin len ≃ Fin N) : ((j : Fin p) × Fin (multiSize len part j)) ≃ Fin N :=
  (((sigmaCongrU fun j ↦ multiSplitPos len part j).trans
      (Equiv.sigmaProdDistrib (fun j ↦ Fin (multiCount part j)) (Fin len)).symm).trans
    (prodCongrU (Fin len) (multiBlocks part))).trans pos

end MME.MultiSplit


