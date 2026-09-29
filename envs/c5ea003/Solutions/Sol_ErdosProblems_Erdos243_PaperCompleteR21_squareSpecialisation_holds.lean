-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR21.squareSpecialisation_holds
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:48:43.87603+00:00
-- url     : https://prove2.me/submissions/55dbd4f9-7955-4f02-b7bb-7a0b71722493

import Definitions.Def_ErdosProblems_Shared_DirichletPoleComparison
import Definitions.Def_ErdosProblems_Shared_IdealCountingEuler
import Definitions.Def_ErdosProblems_Shared_QuadraticSplitPrimes
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR21_SquareSpecialisationDedekind
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR21_sq_sub_dvd_of_modular_squares
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
end ErdosProblems.Erdos243.PaperCompleteR21

open NumberField Polynomial
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR21 in
theorem solution :
    ∀ (L₀ : Type) [Field L₀] [Algebra ℚ L₀] (α : L₀) (f H : Polynomial ℚ),
      Irreducible f → Polynomial.aeval α f = 0 → Polynomial.aeval α H ≠ 0 →
      ∀ (d : ℕ), 0 < d → ∀ G J : Polynomial ℤ,
      G.map (Int.castRingHom ℚ) = Polynomial.C (d : ℚ) * f →
      J.map (Int.castRingHom ℚ) = Polynomial.C ((d : ℚ) ^ 2) * H →
      (∃ N : ℕ, ∀ ℓ : ℕ, ℓ.Prime → N < ℓ → ∀ r : ZMod ℓ,
          (G.map (Int.castRingHom (ZMod ℓ))).eval r = 0 →
          (J.map (Int.castRingHom (ZMod ℓ))).eval r ≠ 0 ∧
            IsSquare ((J.map (Int.castRingHom (ZMod ℓ))).eval r)) →
      ∃ β ∈ IntermediateField.adjoin ℚ ({α} : Set L₀),
        β ≠ 0 ∧ β ^ 2 = Polynomial.aeval α H := by
  intro L₀ _ _ α f H hf hfα hHα d hd G J hG hJ hmod
  obtain ⟨B, hB⟩ := sq_sub_dvd_of_modular_squares f H hf d hd G J hG hJ hmod
  have hsq : Polynomial.aeval α B ^ 2 = Polynomial.aeval α H := by
    obtain ⟨q, hq⟩ := hB
    have h1 : Polynomial.aeval α (B ^ 2 - H) = Polynomial.aeval α (f * q) := by rw [hq]
    rw [map_sub, map_pow, map_mul, hfα, zero_mul, sub_eq_zero] at h1
    exact h1
  refine ⟨Polynomial.aeval α B, ?_, ?_, hsq⟩
  · have hmem : Polynomial.aeval α B ∈ Algebra.adjoin ℚ ({α} : Set L₀) := by
      rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range]
      exact ⟨B, rfl⟩
    have hle : Algebra.adjoin ℚ ({α} : Set L₀)
        ≤ (IntermediateField.adjoin ℚ ({α} : Set L₀)).toSubalgebra :=
      Algebra.adjoin_le fun x hx => IntermediateField.subset_adjoin ℚ _ hx
    exact hle hmem
  · intro h
    apply hHα
    rw [← hsq, h]
    ring
