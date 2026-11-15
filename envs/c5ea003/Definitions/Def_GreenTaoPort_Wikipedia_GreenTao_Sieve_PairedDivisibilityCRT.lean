-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:57:18.53235+00:00
-- url     : https://prove2.me/theorems/9b56dfdd-e5b7-4da7-87f5-cf066dcedce3
-- title:
--   Prime-power CRT coordinates for paired divisibility
-- statement:
--   Each form index with divisor pair $(d_q,e_q)$ has local modulus $\operatorname{lcm}(d_q,e_q)$. For a positive global modulus $D$, the coordinatewise Chinese remainder equivalence identifies a residue vector modulo $D$ with one vector modulo $p^{v_p(D)}$ for every prime divisor $p$ of $D$. A general dependent-function transpose equivalence supplies the required reordering of coordinates.
--
--   The factorization predicate states exactly that the global paired-divisibility indicator equals the product of the prescribed local real factors evaluated on these canonical prime-power components. It is a hypothesis connecting the given natural-valued evaluations with local factors, rather than a claim about arbitrary evaluation functions.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/PairedDivisibilityCRT.lean#L36-L489

import Mathlib.Data.ZMod.QuotientRing
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
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
# CRT factorization of paired divisibility densities

The divisor expansion of a product of Selberg weights leaves an exact finite
density `pairedDivisibilityDensity`.  This file isolates the arithmetic steps
which can be performed without any analytic estimate.

First, the two divisor conditions attached to one form are replaced by their
least common multiple.  The resulting zero--one function is identified with
the indicator of its exact finite support, and each nonzero local modulus is
then decomposed into its prime-power divisibility conditions.

Second, normalized means are reindexed by the Chinese remainder theorem.
For any finite pairwise-coprime family of moduli, a product of functions which
depends separately on the corresponding CRT components has mean equal to the
product of its local means.  We specialize this both to two moduli and to the
canonical prime-power decomposition of a nonzero modulus.

For arbitrary natural-valued forms, CRT factorization is not automatic: one
must still show that the global paired divisibility indicator depends on the
CRT components as a product of local indicators.  The final definitions and
theorems package precisely that remaining obligation, without asserting a
false independence statement.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Collapsing paired divisibility conditions -/

/-- The least common multiple of the two divisor choices attached to one
member of the family. -/
def pairedLocalModulus
    {κ : Type*} (z : κ → ℕ × ℕ) (q : κ) : ℕ :=
  Nat.lcm (z q).1 (z q).2







/-- The LCM of all paired choices is the LCM of the per-form local moduli. -/
theorem pairedDivisorLcm_eq_lcm_pairedLocalModulus
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (z : κ → ℕ × ℕ) :
    pairedDivisorLcm z =
      Finset.univ.lcm (pairedLocalModulus z) := by
  apply Nat.dvd_antisymm
  · rw [pairedDivisorLcm, Finset.lcm_dvd_iff]
    intro q _hq
    cases q with
    | inl q =>
        exact (Nat.dvd_lcm_left (z q).1 (z q).2).trans
          (Finset.dvd_lcm (f := pairedLocalModulus z)
            (Finset.mem_univ q))
    | inr q =>
        exact (Nat.dvd_lcm_right (z q).1 (z q).2).trans
          (Finset.dvd_lcm (f := pairedLocalModulus z)
            (Finset.mem_univ q))
  · rw [Finset.lcm_dvd_iff]
    intro q _hq
    rw [pairedLocalModulus, Nat.lcm_dvd_iff]
    constructor
    · exact Finset.dvd_lcm
        (f := Sum.elim (fun i => (z i).1) (fun i => (z i).2))
        (Finset.mem_univ (Sum.inl q))
    · exact Finset.dvd_lcm
        (f := Sum.elim (fun i => (z i).1) (fun i => (z i).2))
        (Finset.mem_univ (Sum.inr q))









/-! ## Prime-power divisibility data -/

/-- A prime occurring in a natural-number factorization is nonzero.  This
instance lets the finite `ZMod` API infer finiteness at the associated prime
powers. -/
instance neZero_coe_primeFactor
    {D : ℕ} (p : D.primeFactors) : NeZero (p : ℕ) :=
  ⟨(Nat.prime_of_mem_primeFactors p.2).ne_zero⟩







/-! ## Exact factorization of finite means by CRT -/

/-- Transpose two dependent function coordinates. -/
def piSwapEquiv
    {ι τ : Type*} {α : ι → τ → Type*} :
    (∀ i, ∀ t, α i t) ≃ (∀ t, ∀ i, α i t) where
  toFun x t i := x i t
  invFun x i t := x t i
  left_inv _ := rfl
  right_inv _ := rfl

















/-! ## Canonical prime-power CRT -/

/-- Coordinatewise CRT for the canonical prime-power factorization of a
nonzero modulus. -/
noncomputable def coordinatePrimePowerEquiv
    {ι : Type*} {D : ℕ} [NeZero D] :
    (ι → ZMod D) ≃
      (∀ p : D.primeFactors,
        ι → ZMod ((p : ℕ) ^ D.factorization p)) :=
  (Equiv.piCongrRight fun _ =>
      (ZMod.equivPi D (NeZero.ne D)).toEquiv).trans
    piSwapEquiv



/-! ## Conditional factorization interfaces for paired densities -/





/-- The exact hypothesis needed to factor a paired indicator over the
canonical prime-power CRT decomposition of a nonzero modulus. -/
def PairedDivisibilityFactorsOverPrimePowers
    {κ ι : Type*} [Fintype κ]
    {D : ℕ} [NeZero D]
    (values : κ → (ι → ZMod D) → ℕ)
    (z : κ → ℕ × ℕ)
    (localFactor :
      ∀ p : D.primeFactors,
        (ι → ZMod ((p : ℕ) ^ D.factorization p)) → ℝ) : Prop :=
  ∀ x,
    pairedDivisibilityIndicator values z x =
      ∏ p, localFactor p (coordinatePrimePowerEquiv x p)



end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.pairedLocalModulus.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


