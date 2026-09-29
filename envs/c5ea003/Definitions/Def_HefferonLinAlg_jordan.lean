-- Prove2me | Definitions.Def_HefferonLinAlg_jordan
-- name    : HefferonLinAlg_jordan
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-08-07T03:56:45.148005+00:00
-- url     : https://prove2.me/theorems/fcadae98-3f3c-4ce3-a540-0cdfc61ee2b6
-- title:
--   Matrix similarity, Jordan blocks, and Jordan matrices
-- statement:
--   The vocabulary of Hefferon's Chapter Five, Section IV.2, stated over an arbitrary commutative ring and an arbitrary finite index type so that later work can reuse it: only the theorems need $\mathbb{C}$. **Similarity** is factored out as its own definition ($B = P^{-1}AP$ for some $P$ of unit determinant), so statements about similarity alone can be phrased against it. A **Jordan block** of size $m$ with eigenvalue $\lambda$ is the $m \times m$ matrix carrying $\lambda$ down the diagonal and $1$ on the subdiagonal; Hefferon places the ones *below* the diagonal, matching his convention that a nilpotent map carries each string basis vector to the next. A **Jordan matrix** is assembled from finitely many such blocks: given a block count $k$, sizes $sz : \mathrm{Fin}\,k \to \mathbb{N}$ and eigenvalues $\lambda : \mathrm{Fin}\,k \to \mathbb{C}$, it is indexed by $\Sigma\, i,\ \mathrm{Fin}(sz\,i)$ and is the block diagonal of those blocks. The block data is a **Jordan form of** $A$ when every block is nonempty and, after a reindexing of the coordinates, some change of basis carries $A$ to that Jordan matrix; $A$ **has a Jordan form** when such data exists. Nonemptiness is what makes the data an invariant -- without it one could pad any Jordan form with empty blocks carrying arbitrary eigenvalues. Finally `jordanBlocks` is the multiset of $(\text{size}, \text{eigenvalue})$ pairs, which is what discards the ordering of the blocks.
-- source:
--   Jim Hefferon, *Linear Algebra*, Saint Michael's College, 2020 printing, Chapter Five, Section IV.2, printed pp. 448-463 (PDF pp. 458-473)

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace HefferonLinAlg

open Matrix

variable {R : Type*}

/-- Two square matrices are **similar** when a change of basis carries one to the
other: `B = P⁻¹ A P` for some `P` with unit determinant.  Kept separate from the
Jordan-form vocabulary below so that any statement about matrix similarity — that
it is an equivalence relation, that it preserves the determinant, trace, rank or
characteristic polynomial — can be phrased against it. -/
def IsSimilar [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι R) : Prop :=
  ∃ P : Matrix ι ι R, IsUnit P.det ∧ P⁻¹ * A * P = B

/-- The `m × m` **Jordan block** with eigenvalue `lam`: `lam` down the diagonal and
`1` on the subdiagonal.  Hefferon puts the ones *below* the diagonal (Five.IV.2),
matching the book's convention that a nilpotent map carries each string basis
vector to the next one.  Stated over an arbitrary scalar type so that the same
block is available for real, rational or general-field Jordan theory. -/
def jordanBlock [Zero R] [One R] (m : ℕ) (lam : R) : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun i j => if i = j then lam else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0

@[simp] theorem jordanBlock_apply [Zero R] [One R] {m : ℕ} (lam : R) (i j : Fin m) :
    jordanBlock m lam i j =
      if i = j then lam else if (i : ℕ) = (j : ℕ) + 1 then 1 else 0 :=
  rfl

/-- The index type of a Jordan matrix with `k` blocks of sizes `sz`. -/
abbrev jordanIndex {k : ℕ} (sz : Fin k → ℕ) : Type := Σ i : Fin k, Fin (sz i)

/-- The block-diagonal **Jordan matrix** with `k` blocks, the `i`-th of size `sz i`
and eigenvalue `lam i`. -/
def jordanMatrix [Zero R] [One R] {k : ℕ} (sz : Fin k → ℕ) (lam : Fin k → R) :
    Matrix (jordanIndex sz) (jordanIndex sz) R :=
  Matrix.blockDiagonal' fun i => jordanBlock (sz i) (lam i)

@[simp] theorem jordanMatrix_apply_same [Zero R] [One R] {k : ℕ}
    (sz : Fin k → ℕ) (lam : Fin k → R) (i : Fin k) (a b : Fin (sz i)) :
    jordanMatrix sz lam ⟨i, a⟩ ⟨i, b⟩ = jordanBlock (sz i) (lam i) a b := by
  simp [jordanMatrix, Matrix.blockDiagonal'_apply_eq]

@[simp] theorem jordanMatrix_apply_ne [Zero R] [One R] {k : ℕ}
    (sz : Fin k → ℕ) (lam : Fin k → R) {i j : Fin k}
    (a : Fin (sz i)) (b : Fin (sz j)) (h : i ≠ j) :
    jordanMatrix sz lam ⟨i, a⟩ ⟨j, b⟩ = 0 := by
  simp [jordanMatrix, Matrix.blockDiagonal'_apply_ne _ _ _ h]

/-- The block data `(sz, lam)` **is a Jordan form of** `A`: every block is nonempty,
and after reindexing the coordinates by `e`, `A` is similar to the corresponding
block-diagonal Jordan matrix.

Nonemptiness (`0 < sz i`) is what makes the block data an invariant: without it one
could pad any Jordan form with empty blocks carrying arbitrary eigenvalues, and no
uniqueness statement could hold. -/
def IsJordanFormOf [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (A : Matrix ι ι R) (sz : Fin k → ℕ) (lam : Fin k → R) : Prop :=
  (∀ i, 0 < sz i) ∧
    ∃ e : ι ≃ jordanIndex sz,
      IsSimilar A (Matrix.reindex e.symm e.symm (jordanMatrix sz lam))

/-- `A` **has a Jordan form**: it is similar to a block-diagonal Jordan matrix.
Note this says `A` is *similar to* a Jordan matrix, not that `A` is one. -/
def HasJordanForm [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) : Prop :=
  ∃ (k : ℕ) (sz : Fin k → ℕ) (lam : Fin k → R), IsJordanFormOf A sz lam

/-- The multiset of `(block size, eigenvalue)` pairs of a Jordan form. Passing to a
multiset is exactly what discards the ordering of the blocks, which is the sense in
which Jordan form is unique (Hefferon, Five.IV.2, Remark 2.9). -/
def jordanBlocks {k : ℕ} (sz : Fin k → ℕ) (lam : Fin k → R) : Multiset (ℕ × R) :=
  (Finset.univ : Finset (Fin k)).val.map fun i => (sz i, lam i)

/-- The dimension of the kernel of `(A - lam)^r`.  As `r` grows these dimensions
determine how many Jordan blocks of each size carry the eigenvalue `lam`, so they
are the invariant behind uniqueness of the Jordan form; they are also the standard
way to read block structure off a matrix in practice. -/
noncomputable def kerDim {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (lam : K) (r : ℕ) : ℕ :=
  Module.finrank K (LinearMap.ker (Matrix.toLin' ((A - lam • 1) ^ r)))

end HefferonLinAlg


