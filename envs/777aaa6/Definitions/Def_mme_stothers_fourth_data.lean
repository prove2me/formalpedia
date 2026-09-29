-- Prove2me | Definitions.Def_mme_stothers_fourth_data
-- name    : mme_stothers_fourth_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-29T00:19:29.685719+00:00
-- url     : https://prove2.me/theorems/b4a01c01-ee2b-48ff-be25-ca5ec69d6971
-- title:
--   Davie--Stothers fourth-power data
-- statement:
--   This definition module records the finite data used by the Davie--Stothers fourth-power analysis.
--
--   It defines the literal parenthesized tensor
--
--   $$
--   (CW_q\otimes CW_q)\otimes(CW_q\otimes CW_q),
--   $$
--
--   its canonical grading by mode grades $0,\ldots,8$, and every literal graded constituent. It also records the ten Table 1 representatives
--   $008,017,026,035,044,116,125,134,224,233$, their multiplicities, and their ten cubed value expressions using $\rho=3\tau$.
--
--   Finally, it defines Equation (5.2)'s $9\times10$ marginal map, the two displayed kernel vectors, the normalized frequency set $Z$, the corrected stationary set $\mathcal N$, the entropy product in Lemma 5.2, and the complete right-hand side of Equation (5.3).
--
--   **Formalization Note** The journal's printed equations for $\mathcal N$ are inconsistent with its displayed kernel and numerical data. `InN` uses the stationarity equations derived in Stothers's thesis, Chapter 4.2, pp. 78--79. The definition module is sorry-free and asserts no constituent value theorem.
-- source:
--   Davie and Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Section 5, Lemma 5.1, Tables 1-2, Equation (5.2), Lemma 5.2, Equation (5.3), printed pp. 363-368, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; corrected stationarity equations: Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.2, printed pp. 78-81, https://era.ed.ac.uk/bitstream/1842/4734/1/Stothers2010.pdf.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Definitions.Def_mme_CW_square_canonical_grading

/-!
# Source data for the Davie--Stothers fourth-power argument

This module records the literal fourth Coppersmith--Winograd power and the
finite data in Section 5 of Davie--Stothers.  It contains definitions only:
in particular, none of the constituent value bounds from Lemma 5.1 or the
global value inequality from Theorem 5.3 is assumed here.

The paper writes `rho` for the candidate matrix-multiplication exponent.
The platform's tau-value normalization is `rho = 3 * tau`, which is used in
`E`, `H`, `L`, and `classValue` below.
-/

open MME TensorProduct Module BigOperators

universe u

namespace MME.StothersFourth

set_option autoImplicit false

/-! ## The literal fourth power and its canonical nine-grading -/

/-- The parenthesized fourth power `(CW_q ⊗ CW_q) ⊗ (CW_q ⊗ CW_q)`.
This is the literal tensor used in Section 5, not a formal sum of its graded
constituents. -/
noncomputable def cwFourthObj
    (K : Type u) [Field K] (q : ℕ) : TensorObj K 3 :=
  TensorObj.kron
    (TensorObj.kron (CWObj K q) (CWObj K q))
    (TensorObj.kron (CWObj K q) (CWObj K q))

/-- Grade of a fourth-power basis coordinate.  It is the sum of the grades
of the two square coordinates, and hence lies in `{0, ..., 8}`. -/
def cwFourthPairGrade (q : ℕ)
    (p :
      (Fin (q + 2) × Fin (q + 2)) ×
      (Fin (q + 2) × Fin (q + 2))) : Fin 9 :=
  ⟨(cwSquarePairGrade q p.1).val + (cwSquarePairGrade q p.2).val, by
    omega⟩

private instance fourthScalarTower
    {K : Type u} [Field K] (V : Type u)
    [AddCommGroup V] [Module K V] : IsScalarTower K K V :=
  IsScalarTower.of_algebraMap_smul (by simp)

/-- Tensor-product basis used to form the nine graded pieces in each mode. -/
noncomputable def cwFourthCanonicalBasis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) :
    Basis
      ((Fin (q + 2) × Fin (q + 2)) ×
       (Fin (q + 2) × Fin (q + 2)))
      K ((cwFourthObj K q).V s) := by
  exact Module.Basis.tensorProduct
    (cwSquareCanonicalBasis K q s)
    (cwSquareCanonicalBasis K q s)

/-- The canonical nine-grading of the literal fourth power. -/
noncomputable def cwFourthCanonicalGrading
    (K : Type u) [Field K] (q : ℕ) :
    (cwFourthObj K q).TypeGrading 9 where
  decomp s := cwBasisGrade (cwFourthCanonicalBasis K q s)
    (cwFourthPairGrade q)
  is_internal s := cwBasisGrade_isInternal
    (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q)

/-- A grade triple `(I,J,L)` as a block type for an order-three tensor. -/
def cwFourthBlockType (I J L : Fin 9) : Fin 3 → Fin 9
  | ⟨0, _⟩ => I
  | ⟨1, _⟩ => J
  | ⟨2, _⟩ => L

/-- The literal `(I,J,L)` block constituent of `CW_q^4`. -/
noncomputable def cwFourthConstituent
    (K : Type u) [Field K] (q : ℕ) (I J L : Fin 9) : TensorObj K 3 :=
  (cwFourthCanonicalGrading K q).blockSubtensor
    (cwFourthBlockType I J L)

/-! ## Table 1 symmetry classes -/

/-- The ten representatives in Table 1, in the source order
`008, 017, 026, 035, 044, 116, 125, 134, 224, 233`. -/
def classRep : Fin 10 → Fin 3 → Fin 9 :=
  ![cwFourthBlockType 0 0 8,
    cwFourthBlockType 0 1 7,
    cwFourthBlockType 0 2 6,
    cwFourthBlockType 0 3 5,
    cwFourthBlockType 0 4 4,
    cwFourthBlockType 1 1 6,
    cwFourthBlockType 1 2 5,
    cwFourthBlockType 1 3 4,
    cwFourthBlockType 2 2 4,
    cwFourthBlockType 2 3 3]

/-- Table 1's `n_i`.  The full permutation class contains `3 * n_i`
constituents. -/
def classMultiplicity : Fin 10 → ℕ :=
  ![1, 2, 2, 2, 1, 1, 2, 2, 1, 1]

/-- Two grade triples lie in the same class when a permutation of the three
tensor modes takes one to the other. -/
def sameOrbit (σ ρ : Fin 3 → Fin 9) : Prop :=
  ∃ e : Equiv.Perm (Fin 3), ∀ s, σ s = ρ (e s)

/-- The orbit relation is finite and hence classically decidable.  Exporting
this instance lets finite class-cardinality statements use subtype notation
without adding local `classical` boilerplate. -/
noncomputable instance instDecidableSameOrbit
    (σ ρ : Fin 3 → Fin 9) : Decidable (sameOrbit σ ρ) :=
  Classical.propDecidable _

/-! ## Lemma 5.1 and Table 1 numerical data -/

/-- `E = (2q)^rho`, with `rho = 3 * tau`. -/
noncomputable def E (q : ℕ) (tau : ℝ) : ℝ :=
  ((2 * q : ℕ) : ℝ) ^ (3 * tau)

/-- `H = (q^2 + 2)^rho`, with `rho = 3 * tau`. -/
noncomputable def H (q : ℕ) (tau : ℝ) : ℝ :=
  (((q : ℝ) ^ (2 : ℕ)) + 2) ^ (3 * tau)

/-- `L = 4 q^rho (q^rho + 2)`, with `rho = 3 * tau`. -/
noncomputable def L (q : ℕ) (tau : ℝ) : ℝ :=
  4 * (q : ℝ) ^ (3 * tau) * ((q : ℝ) ^ (3 * tau) + 2)

/-- The ten `v_i` in Table 1.  Each entry is the *cube* of the
corresponding constituent-value lower bound. -/
noncomputable def classValue (q : ℕ) (tau : ℝ) : Fin 10 → ℝ :=
  ![1,
    (4 * (q : ℝ)) ^ (3 * tau),
    (6 * (q : ℝ) ^ (2 : ℕ) + 4) ^ (3 * tau),
    (4 * (q : ℝ) * ((q : ℝ) ^ (2 : ℕ) + 3)) ^ (3 * tau),
    ((q : ℝ) ^ (4 : ℕ) + 12 * (q : ℝ) ^ (2 : ℕ) + 6) ^
      (3 * tau),
    4 * (E q tau ^ (2 : ℕ) + 2 * L q tau),
    4 * (L q tau + E q tau * H q tau) * (2 * H q tau + L q tau) /
      H q tau,
    4 * (E q tau + L q tau) * (2 + 2 * E q tau + H q tau),
    (2 * H q tau + L q tau) ^ (2 : ℕ) *
      (2 + 2 * E q tau + H q tau) / H q tau,
    4 * (E q tau + L q tau) ^ (2 : ℕ) *
      (2 * H q tau + L q tau) / L q tau]

/-! ## Equation (5.2), its kernel, and the feasible sets -/

/-- The `9 × 10` marginal map `Q` displayed in Equation (5.2).
Lean indices are zero-based: `a 0` is the paper's `alpha_1`. -/
def Q (a : Fin 10 → ℝ) : Fin 9 → ℝ :=
  ![2 * a 0 + 2 * a 1 + 2 * a 2 + 2 * a 3 + a 4,
    2 * a 1 + 2 * a 5 + 2 * a 6 + 2 * a 7,
    2 * a 2 + 2 * a 6 + 2 * a 8 + a 9,
    2 * a 3 + 2 * a 7 + 2 * a 9,
    2 * a 4 + 2 * a 7 + a 8,
    2 * a 3 + 2 * a 6,
    2 * a 2 + a 5,
    2 * a 1,
    a 0]

/-- The first displayed kernel vector after Equation (5.2). -/
def kernelSigma : Fin 10 → ℝ :=
  ![0, 0, 1, 0, -2, -2, 0, 2, 0, -2]

/-- The second displayed kernel vector after Equation (5.2). -/
def kernelTau : Fin 10 → ℝ :=
  ![0, 0, 0, 1, -2, 0, -1, 1, 2, -2]

/-- The normalized frequency simplex `Z` from Section 5. -/
def InZ (a : Fin 10 → ℝ) : Prop :=
  (∀ i, 0 ≤ a i) ∧
    ∑ i, (classMultiplicity i : ℝ) * a i = 1

/-- The literal kernel predicate `Qx = 0`. -/
def InKernelQ (x : Fin 10 → ℝ) : Prop :=
  ∀ j, Q x j = 0

/-- The displayed two-dimensional parametrization of the kernel `Y` by the
vectors `kernelSigma` and `kernelTau`. -/
def InY (x : Fin 10 → ℝ) : Prop :=
  ∃ s t : ℝ, ∀ i,
    x i = s * kernelSigma i + t * kernelTau i

/-- The algebraic subset `N` used by Lemma 5.2.

The journal's printed equations on p. 368 are a typo: they do not follow
from its displayed kernel and are not satisfied by its numerical optimizer.
These are the stationarity equations derived on pp. 78--79 of Stothers's
thesis, translated to the journal's class order (the thesis swaps the final
two classes). -/
def InN (a : Fin 10 → ℝ) : Prop :=
  InZ a ∧
    a 2 * a 7 ^ (2 : ℕ) = a 4 * a 5 * a 9 ∧
    a 3 * a 7 * a 8 = a 4 * a 6 * a 9

/-- The paper's marginal vector `A = (1/3) Qa`. -/
noncomputable def marginal (a : Fin 10 → ℝ) (j : Fin 9) : ℝ :=
  Q a j / 3

/-! ## Lemma 5.2 entropy and Equation (5.3) -/

/-- The weighted product compared in Lemma 5.2:
`prod_i a_i^(n_i a_i)`. -/
noncomputable def entropyProduct (a : Fin 10 → ℝ) : ℝ :=
  ∏ i, Real.rpow (a i) ((classMultiplicity i : ℝ) * a i)

/-- The complete right-hand side of Equation (5.3), in the normalization
`rho = 3 * tau`.  The `v_i` supplied by `classValue` are already cubed,
which accounts for the exponent `a_i / 3`. -/
noncomputable def globalRate
    (q : ℕ) (tau : ℝ) (a b : Fin 10 → ℝ) : ℝ :=
  (∏ i,
      (Real.rpow (classValue q tau i) (a i / 3) *
        Real.rpow (a i) (a i) *
        Real.rpow (b i) (-b i)) ^ classMultiplicity i) *
    ∏ j, Real.rpow (marginal a j) (-marginal a j)

end MME.StothersFourth


