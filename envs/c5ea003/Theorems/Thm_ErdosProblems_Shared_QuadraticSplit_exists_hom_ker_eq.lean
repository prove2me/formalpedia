-- Prove2me | Theorems.Thm_ErdosProblems_Shared_QuadraticSplit_exists_hom_ker_eq
-- name    : ErdosProblems.Shared.QuadraticSplit.exists_hom_ker_eq
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:54:28.512917+00:00
-- url     : https://prove2.me/theorems/6ae74bea-f6c0-4e5c-8b90-c16360506976
-- title:
--   Lean source theorem: exists_hom_ker_eq
-- statement:
--   A prime ideal of norm equal to a prime ℓ is the kernel of some ring homomorphism from the integer ring to ℤ/ℓℤ.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Shared/QuadraticSplitPrimes.lean#L275-L288
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Shared_QuadraticSplitPrimes
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Trace.Basic

/-!
# Degree-one primes that split in a quadratic extension

Let `K ⊆ M` be number fields with `[M : K] = 2` and `M = K(γ)`, `γ ^ 2 = b ∈ 𝓞 K`.  A ring
homomorphism `φ : 𝓞 K → ZMod ℓ` (`ℓ` an odd prime) with `φ b = t ^ 2`, `t ≠ 0`, extends to two
distinct ring homomorphisms `𝓞 M → ZMod ℓ`, sending `γ` to `t` and to `-t`.

The ring of integers of `M` is not described explicitly.  Instead every `x ∈ M` satisfies

`2 b x = b · Tr(x) + Tr(γ x) · γ`        (`Tr = Tr_{M/K}`),

because `x = u + v γ` with `Tr x = 2 u` and `Tr (γ x) = 2 b v`.  For `x ∈ 𝓞 M` both traces lie in
`𝓞 K`, so `x ↦ (φ b · φ (Tr x) + φ (Tr (γ x)) · t) / (2 φ b)` is defined on `𝓞 M`; it is
multiplicative because of the two trace identities `trace_identity_one` and
`trace_identity_two`, which follow from the displayed formula.

The kernels of the two extensions are two distinct primes of `𝓞 M` of norm `ℓ`, both lying over
the kernel of `φ`.  `exists_split_primes_of_forall_isSquare` packages this in the form consumed by
`ErdosProblems.Shared.IdealCounting.sum_countSupp_mul_le`.
-/

noncomputable section


open NumberField Polynomial

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

/-! ### The quadratic extension `M = K(γ)` -/















/-! ### The two extensions of `φ` to `𝓞 M` -/









/-! ### Kernels -/

open ErdosProblems.Shared.QuadraticSplit

theorem ErdosProblems.Shared.QuadraticSplit.exists_hom_ker_eq {ℓ : ℕ} (hℓ : ℓ.Prime) (𝔭 : Ideal (𝓞 K))
    (h : Ideal.absNorm 𝔭 = ℓ) : ∃ φ : 𝓞 K →+* ZMod ℓ, RingHom.ker φ = 𝔭 := by sorry
