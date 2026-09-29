-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR21_SquareSpecialisationDedekind
-- name    : ErdosProblems_Erdos243_PaperCompleteR21_SquareSpecialisationDedekind
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T19:11:39.290996+00:00
-- url     : https://prove2.me/theorems/0a420088-510e-4dd7-bef1-b8bbd8c7cbaa
-- title:
--   Scaled polynomial evaluation
-- statement:
--   Defines scaledEval for an integer polynomial, integer scale, exponent and value in a commutative ring.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR21/SquareSpecialisationDedekind.lean#L1-L220
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Shared_DirichletPoleComparison
import Definitions.Def_ErdosProblems_Shared_IdealCountingEuler
import Definitions.Def_ErdosProblems_Shared_QuadraticSplitPrimes
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Polynomial.IntegralNormalization
import Mathlib.RingTheory.Trace.Basic

/-!
# Erdős 243: the square-specialisation lemma without the Chebotarev density theorem

Paper form of `long243:res:squarespec` of `paper/reasoning-parts/erdos243/core.tex`
(lemma at line 303): `f ∈ ℚ[T]` irreducible with root `α`, `H (α) ≠ 0`, and for all but finitely
many primes `ℓ` every root `r` of `f` modulo `ℓ` has `H (r)` a nonzero square modulo `ℓ`
(stated through integral models `G = d f`, `J = d ^ 2 H`); then `H (α)` is a square in `ℚ(α)`.

The paper derives this from the Chebotarev density theorem.  Here it follows from
`ErdosProblems.Shared.NonsquareModuloPrimes.exists_prime_hom_not_isSquare`, whose only analytic
input is the simple pole of the Dedekind zeta function at `s = 1`, already in Mathlib.

The reduction.  Put `K = ℚ[T] / (f)` with `α` the class of `T`, and `c` the leading coefficient
of `G`.  Then `a = c α` is integral, and for a polynomial `P ∈ ℤ[T]` and `e ≥ deg P` the element
`∑_{j ≤ e} P_j c ^ (e - j) a ^ j` of `𝓞 K` equals `c ^ e P (α)`; under any ring homomorphism
`φ : 𝓞 K → ZMod ℓ` it becomes `c ^ e P (r)` with `r = φ (a) / c`.  Taking `P = G` shows that
`r` is a root of `G` modulo `ℓ`, and taking `P = J`, `e = 2 deg J`, gives an element
`b = (c ^ (deg J) d) ^ 2 H (α)` of `𝓞 K` with `φ (b) = (c ^ (deg J)) ^ 2 J (r)`.  If `H (α)` were
not a square in `K`, neither would `b` be, and some prime `ℓ` beyond every bound would make
`φ (b)` zero or a non-square, contradicting the hypothesis at the root `r`.

`squareSpecialisation_holds` is the statement of
`ErdosProblems.Erdos243.PaperCompleteR21.SquareSpecialisation` written out in full, so this file
depends on Mathlib and the `Shared` number-field files only.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR21

open NumberField Polynomial

/-- `∑_{j ≤ e} P_j c ^ (e - j) a ^ j`: the value at `a` of `c ^ e P (T / c)`. -/
def scaledEval {R : Type*} [CommRing R] (P : Polynomial ℤ) (c : ℤ) (e : ℕ) (a : R) : R :=
  ∑ j ∈ Finset.range (e + 1), ((P.coeff j * c ^ (e - j) : ℤ) : R) * a ^ j














end ErdosProblems.Erdos243.PaperCompleteR21


