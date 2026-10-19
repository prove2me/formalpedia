-- Prove2me | Theorems.Thm_Williamson_array
-- name    : Williamson_array
-- status  : Proved
-- author  : @ronr
-- created : 2026-09-06T00:55:11.553826+00:00
-- url     : https://prove2.me/theorems/150f7786-c4d5-4a97-bb3e-15d34236a271
-- title:
--   Williamson's array: four commuting symmetric $\pm1$ matrices give a Hadamard matrix
-- statement:
--   This is Williamson's array construction, the standard route to Hadamard matrices beyond the Sylvester and Paley families.
--
--   Let $n=|\iota|$ and let $A,B,C,D$ be $n\times n$ real matrices such that:
--
--   1. every entry of each is $1$ or $-1$;
--   2. each is symmetric, $A^{\mathsf T}=A$ and likewise for $B,C,D$;
--   3. they commute pairwise; and
--   4. their squares satisfy $A^{2}+B^{2}+C^{2}+D^{2}=4n\,I_{n}$.
--
--   Then there is a Hadamard matrix of order $4n$: a $4n\times4n$ matrix $M$ with all entries $\pm1$ and $MM^{\mathsf T}=4n\,I_{4n}$.
--
--   **The construction.** $M$ is the Williamson array
--
--   $$
--   M=\begin{pmatrix} A & B & C & D\\ -B & A & -D & C\\ -C & D & A & -B\\ -D & -C & B & A\end{pmatrix},
--   $$
--
--   which has the nested form $\begin{pmatrix}P&Q\\-Q^{\mathsf T}&P^{\mathsf T}\end{pmatrix}$ with $P=\begin{pmatrix}A&B\\-B&A\end{pmatrix}$ and $Q=\begin{pmatrix}C&D\\-D&C\end{pmatrix}$. The commutativity hypotheses make $P$ and $Q$ commute and force the off-diagonal blocks of $MM^{\mathsf T}$ to vanish, while hypothesis (4) makes each diagonal block equal $4n\,I$.
--
--   **Role.** This theorem supplies no matrices of its own — it is the reusable bridge from a *Williamson quadruple* to a Hadamard matrix. Since Williamson quadruples are known for many orders $n$ not covered by the Sylvester or Paley constructions (the classical first example being $n=23$, giving order $92$), this is the standard next tool for shrinking the residual cases of the Hadamard conjecture.
--
--   **Formalization Note** The index type of the result is $(\iota\oplus\iota)\oplus(\iota\oplus\iota)$, of cardinality $4n$; the array is built with `Matrix.fromBlocks` nested twice, so the whole verification reduces to two applications of a single $2\times2$ block identity plus one commutation lemma. The statement is in orthogonality form, matching the other Hadamard-matrix theorems on this platform.
-- source:
--   J. Williamson, Hadamard's determinant theorem and the sum of four squares, Duke Math. J. 11 (1944), 65-81 (the array and the sum-of-four-squares condition). Standard textbook presentations: K. J. Horadam, Hadamard Matrices and Their Applications, Princeton University Press, 2007, Section 4.1; J. H. van Lint and R. M. Wilson, A Course in Combinatorics, 2nd ed., Cambridge University Press, 2001, Chapter 18. Stated here in orthogonality form, matching Paley_construction_I (65d083bb-43e4-4dfd-a728-69945984f8e0) and Hadamard_matrix_kronecker_product (635fbe02-d442-43c6-b1a0-b7dff65843e0).

import Mathlib
open Matrix

theorem Williamson_array {ι : Type} [Fintype ι] [DecidableEq ι] (A B C D : Matrix ι ι ℝ)
    (hApm : ∀ i j, A i j = 1 ∨ A i j = -1) (hBpm : ∀ i j, B i j = 1 ∨ B i j = -1)
    (hCpm : ∀ i j, C i j = 1 ∨ C i j = -1) (hDpm : ∀ i j, D i j = 1 ∨ D i j = -1)
    (hAs : Aᵀ = A) (hBs : Bᵀ = B) (hCs : Cᵀ = C) (hDs : Dᵀ = D)
    (hAB : A * B = B * A) (hAC : A * C = C * A) (hAD : A * D = D * A)
    (hBC : B * C = C * B) (hBD : B * D = D * B) (hCD : C * D = D * C)
    (hsum : A * A + B * B + C * C + D * D =
      ((4 * Fintype.card ι : ℕ) : ℝ) • (1 : Matrix ι ι ℝ)) :
    ∃ M : Matrix ((ι ⊕ ι) ⊕ (ι ⊕ ι)) ((ι ⊕ ι) ⊕ (ι ⊕ ι)) ℝ,
      (∀ i j, M i j = 1 ∨ M i j = -1) ∧
        M * Mᵀ = ((4 * Fintype.card ι : ℕ) : ℝ) •
          (1 : Matrix ((ι ⊕ ι) ⊕ (ι ⊕ ι)) ((ι ⊕ ι) ⊕ (ι ⊕ ι)) ℝ) := by sorry
