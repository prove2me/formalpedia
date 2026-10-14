-- Prove2me | Definitions.Def_MomentAngle_surgery_blocks
-- name    : MomentAngle_surgery_blocks
-- status  : Definition
-- author  : @Wenqian Xing
-- created : 2026-09-06T11:08:10.324025+00:00
-- url     : https://prove2.me/theorems/39a1a909-15c8-4387-9dd8-6779c880c17b
-- title:
--   Integral presentation for zero-surgery torsion blocks
-- statement:
--   For natural numbers $n,k$, let $A_k=(\mathbb Z^k)^3$ and define an integer homomorphism by
--   $$
--   \Lambda_{n,k}(a,b,c)=(0,nc,nb).
--   $$
--   The surgery presentation group is the cokernel
--   $$
--   C_{n,k}=A_k/\operatorname{im}(\Lambda_{n,k}).
--   $$
--   The matrix is a direct sum of $k$ zero one-dimensional blocks and $k$ blocks $\begin{pmatrix}0&n\\n&0\end{pmatrix}$. It is the linking matrix for the split union of $k$ zero-framed unknots and $k$ zero-framed two-component links of linking number $n$.
--
--   This is an explicit abelian presentation group. Its identification with singular homology of an embedded triangulated manifold is a separate theorem; the definition assumes no topological realization.
-- source:
--   Concrete block-matrix specialization of the integer surgery framing/linking matrix in Danny Calegari, Chapter 6: Floer Theories, Section 1.1.4, Lemma 1.5, printed p. 4, https://math.uchicago.edu/~dannyc/courses/heegaard_2020/floer_theory_notes.pdf . The associated zero-surgery embedding construction is Budney–Burton, arXiv:0810.2346v6, Construction 2.8, printed p. 12, https://arxiv.org/pdf/0810.2346v6 .

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Pi.Lemmas

/-! Integral presentation for k zero-framed unknots and k two-component
links of linking number n. Each nonzero 2-by-2 block is [[0,n],[n,0]]. -/

namespace MomentAngleSurgery

abbrev Generators (k : ℕ) := (Fin k → ℤ) × (Fin k → ℤ) × (Fin k → ℤ)

/-- The integral linking-matrix homomorphism for the split surgery blocks. -/
def linkingMap (n k : ℕ) : Generators k →+ Generators k where
  toFun x := (0, (fun i => (n : ℤ) * x.2.2 i), (fun i => (n : ℤ) * x.2.1 i))
  map_zero' := by ext i <;> simp
  map_add' x y := by ext i <;> simp [mul_add]

/-- The abelian group presented by the explicit surgery linking matrix. -/
abbrev Cokernel (n k : ℕ) := Generators k ⧸ (linkingMap n k).range

end MomentAngleSurgery


