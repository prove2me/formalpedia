-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:58:27.634263+00:00
-- url     : https://prove2.me/theorems/da05d0fd-b590-4db9-aa21-419d071de194
-- title:
--   Squarefree divisor supports and affine prime-local models
-- statement:
--   A paired divisor family is squarefree when both chosen divisors are squarefree at every form index. Its support at a prime $p$ contains exactly the indices whose paired least common multiple is divisible by $p$. The corresponding prime indicator multiplies $p$-divisibility indicators over this support.
--
--   For integer affine forms on a finite variable type and a positive modulus, the bundle supplies the product of zero-congruence indicators, its normalized density, and the explicit common-zero finite set. Under squarefreeness, canonical prime-power CRT coordinates are identified with ordinary prime-modulus coordinates, giving the affine local factor attached to the divisor support.
--
--   The affine-model predicate requires, for every supported form and canonical prime component, equivalence between natural divisibility of its global value and vanishing of its affine prime-residue evaluation. This is the precise compatibility condition used for the local-density factorization.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/PairedLocalFactors.lean#L32-L622

import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Squarefree
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Squarefree paired divisors and finite-family local factors

The Selberg expansion only receives a contribution from squarefree divisor
choices: a nonzero Möbius coefficient forces each of the two divisors attached
to every form to be squarefree.  Consequently all local least common multiples,
and their global least common multiple, are squarefree.  The canonical
prime-power CRT from `PairedDivisibilityCRT` therefore has exponent one at
every prime.

This file records that reduction exactly.  It also packages the local
intersection density of an arbitrary finite subfamily of affine forms.  The
empty, singleton, and two-element cases reduce to the exact APIs in
`LocalFactors`; the full avoidance factor is their finite
inclusion--exclusion sum.  Higher intersections require an additional
arithmetic input, so the final interface exposes that input as a hypothesis
rather than asserting an unavailable estimate.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Squarefree divisor choices -/

/-- Both divisor choices attached to every form are squarefree. -/
def SquarefreePairedDivisorChoice
    {κ : Type*} (z : κ → ℕ × ℕ) : Prop :=
  ∀ q, Squarefree (z q).1 ∧ Squarefree (z q).2



/-- The least common multiple of two squarefree naturals is squarefree. -/
theorem squarefree_nat_lcm
    {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  have hab0 : Nat.lcm a b ≠ 0 := by
    exact Nat.lcm_ne_zero ha.ne_zero hb.ne_zero
  rw [Nat.squarefree_iff_factorization_le_one hab0]
  intro p
  rw [Nat.factorization_lcm ha.ne_zero hb.ne_zero]
  exact sup_le
    (ha.natFactorization_le_one p)
    (hb.natFactorization_le_one p)

/-- Every per-form modulus of a squarefree paired choice is squarefree. -/
theorem squarefree_pairedLocalModulus
    {κ : Type*} {z : κ → ℕ × ℕ}
    (hz : SquarefreePairedDivisorChoice z) (q : κ) :
    Squarefree (pairedLocalModulus z q) := by
  exact squarefree_nat_lcm (hz q).1 (hz q).2

/-- A finite least common multiple of squarefree naturals is squarefree. -/
theorem squarefree_finset_lcm
    {κ : Type*}
    (s : Finset κ) (f : κ → ℕ)
    (hf : ∀ q ∈ s, Squarefree (f q)) :
    Squarefree (s.lcm f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert q s hqs ih =>
      rw [Finset.lcm_insert]
      exact squarefree_nat_lcm
        (hf q (Finset.mem_insert_self q s))
        (ih fun r hr => hf r (Finset.mem_insert_of_mem hr))

/-- The global LCM of a squarefree paired choice is squarefree. -/
theorem squarefree_pairedDivisorLcm
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {z : κ → ℕ × ℕ}
    (hz : SquarefreePairedDivisorChoice z) :
    Squarefree (pairedDivisorLcm z) := by
  rw [pairedDivisorLcm_eq_lcm_pairedLocalModulus]
  exact squarefree_finset_lcm Finset.univ
    (pairedLocalModulus z)
    (fun q _hq => squarefree_pairedLocalModulus hz q)

/-- Every canonical exponent of the global paired LCM is one. -/
theorem pairedDivisorLcm_factorization_eq_one
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {z : κ → ℕ × ℕ}
    (hz : SquarefreePairedDivisorChoice z)
    (p : (pairedDivisorLcm z).primeFactors) :
    (pairedDivisorLcm z).factorization p = 1 := by
  exact Nat.factorization_eq_one_of_squarefree
    (squarefree_pairedDivisorLcm hz)
    (Nat.prime_of_mem_primeFactors p.2)
    (Nat.dvd_of_mem_primeFactors p.2)

/-- Thus the canonical prime-power modulus is literally the prime modulus. -/
theorem pairedDivisorLcm_primePower_eq_prime
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {z : κ → ℕ × ℕ}
    (hz : SquarefreePairedDivisorChoice z)
    (p : (pairedDivisorLcm z).primeFactors) :
    (p : ℕ) ^ (pairedDivisorLcm z).factorization p = p := by
  rw [pairedDivisorLcm_factorization_eq_one hz p, pow_one]

/-! ## Exact prime support and the squarefree indicator product -/

/-- Forms whose paired local modulus contains the prime `p`. -/
def pairedPrimeSupport
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (z : κ → ℕ × ℕ) (p : ℕ) : Finset κ :=
  Finset.univ.filter fun q => p ∣ pairedLocalModulus z q





/-- The local factor carried by a prime in the squarefree paired indicator:
every form in the prime support contributes one divisibility indicator. -/
noncomputable def squarefreePairedPrimeIndicator
    {κ X : Type*} [Fintype κ] [DecidableEq κ]
    (values : κ → X → ℕ) (z : κ → ℕ × ℕ)
    (p : ℕ) (x : X) : ℝ :=
  ∏ q ∈ pairedPrimeSupport z p,
    natDivisibilityIndicator p (values q x)



/-! ## Arbitrary finite-family intersection densities -/

/-- Product of zero-congruence indicators over a selected subfamily. -/
noncomputable def affineFamilyZeroProduct
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) (x : ι → ZMod p) : ℝ :=
  ∏ q ∈ s, finsetIndicator ((forms q).zeroFinsetZMod p) x

/-- The exact normalized density of the common zero set of a selected finite
subfamily. -/
noncomputable def affineFamilyZeroDensity
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) : ℝ :=
  mean (affineFamilyZeroProduct p forms s)

/-- Explicit common-zero support of a selected finite subfamily. -/
def affineFamilyCommonZeroFinset
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) : Finset (ι → ZMod p) :=
  Finset.univ.filter fun x =>
    ∀ q ∈ s, (forms q).evalZMod p x = 0



















/-! ## Exact arbitrary-family local factor formula -/









/-! ## Localization of the canonical CRT factors -/

/-- For a squarefree global LCM, transport a canonical prime-power residue
vector to the corresponding prime residue vector. -/
def squarefreePrimePowerEquiv
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    {z : κ → ℕ × ℕ}
    (hz : SquarefreePairedDivisorChoice z)
    (p : (pairedDivisorLcm z).primeFactors) :
    (ι → ZMod
        ((p : ℕ) ^
          (pairedDivisorLcm z).factorization p)) ≃
      (ι → ZMod (p : ℕ)) :=
  Equiv.cast (by
    rw [pairedDivisorLcm_primePower_eq_prime hz p])

/-- The canonical CRT component, viewed modulo the underlying prime after
the squarefree exponent-one reduction. -/
noncomputable def squarefreeCanonicalPrimeComponent
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    {z : κ → ℕ × ℕ}
    (hz : SquarefreePairedDivisorChoice z)
    (p : (pairedDivisorLcm z).primeFactors)
    (x : ι → ZMod (pairedDivisorLcm z)) :
    ι → ZMod (p : ℕ) := by
  letI : NeZero (pairedDivisorLcm z) :=
    ⟨(squarefree_pairedDivisorLcm hz).ne_zero⟩
  exact squarefreePrimePowerEquiv hz p
    (coordinatePrimePowerEquiv x p)

/-- The canonical prime-local factor attached to an affine system and a
squarefree paired divisor choice. -/
noncomputable def affinePairedPrimeFactor
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (forms : κ → AffineForm ι ℤ)
    (z : κ → ℕ × ℕ)
    (hz : SquarefreePairedDivisorChoice z)
    (p : (pairedDivisorLcm z).primeFactors)
    (x : ι → ZMod
      ((p : ℕ) ^
        (pairedDivisorLcm z).factorization p)) : ℝ :=
  affineFamilyZeroProduct (p : ℕ) forms
    (pairedPrimeSupport z p)
    (squarefreePrimePowerEquiv hz p x)



/-- Concrete sufficient condition connecting natural-valued divisibility
conditions on the global CRT space with the affine zero congruences on each
canonical prime component. -/
def PairedDivisibilityHasAffinePrimeModels
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (z : κ → ℕ × ℕ)
    (values :
      κ → (ι → ZMod (pairedDivisorLcm z)) → ℕ)
    (forms : κ → AffineForm ι ℤ)
    (hz : SquarefreePairedDivisorChoice z) : Prop :=
  ∀ (x : ι → ZMod (pairedDivisorLcm z))
      (p : (pairedDivisorLcm z).primeFactors)
      (q : κ), q ∈ pairedPrimeSupport z p →
    ((p : ℕ) ∣ values q x ↔
        (forms q).evalZMod (p : ℕ)
          (squarefreeCanonicalPrimeComponent hz p x) = 0)









end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.affineFamilyCommonZeroFinset.congr_simp,
    `Wikipedia.SzemeredisTheorem.affineFamilyCommonZeroFinset.eq_1,
    `Wikipedia.SzemeredisTheorem.affineFamilyZeroDensity.congr_simp,
    `Wikipedia.SzemeredisTheorem.affineFamilyZeroDensity.eq_1,
    `Wikipedia.SzemeredisTheorem.affineFamilyZeroProduct.eq_1,
    `Wikipedia.SzemeredisTheorem.pairedPrimeSupport.eq_1,
    `Wikipedia.SzemeredisTheorem.squarefreeCanonicalPrimeComponent.eq_1,
    `Wikipedia.SzemeredisTheorem.squarefreePrimePowerEquiv.congr_simp
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


