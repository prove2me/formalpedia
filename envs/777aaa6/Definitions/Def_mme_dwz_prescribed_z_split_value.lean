-- Prove2me | Definitions.Def_mme_dwz_prescribed_z_split_value
-- name    : mme_dwz_prescribed_z_split_value
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-05T16:03:08.445611+00:00
-- url     : https://prove2.me/theorems/11909636-42bc-4496-a84b-54ded5c2e9fd
-- title:
--   Prescribed Z-split powers and six-symmetric value certificates
-- statement:
--   Let T be an order-three tensor over an arbitrary field, with a chosen basis of its Z-mode and a finite label recording the left grade in the next finer partition. An integer split profile consists of a positive denominator D and nonnegative integer counts c_a summing to D. At each compatible length n=Dm, the prescribed power keeps exactly those Z-basis words in which label a occurs c_a m times. The X and Y modes remain unfiltered.
--
--   A nonnegative value V has a six-symmetric finite-witness certificate when, for every positive v<V and every cutoff, an index m and actual length Dm beyond that cutoff admit a finite direct sum of matrix-multiplication tensors from the six-symmetrization of that prescribed power, with total tau-weight at least v^(6Dm). The definition keeps degeneration witnesses separate from the stronger restriction witnesses. A certified value pair records both the integer profile and the value certified for that profile.
--
--   Formalization Note: this is the rational compatible-length certificate form of Equation (3), designed for exact released witnesses. It does not assert denominator-independence, equivalence with the paper's nested limsup of values, or a definition for irrational distributions. The finite prescribed tensor itself is the literal Z-only projection from Definition 3.9.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/abs/2210.10173, printed pp. 22-24, Definitions 3.7 and 3.9 and Equation (3); p. 72, Definition 8.1. Rational compatible-length finite-witness certificate form; no full limsup-equivalence assertion.

import Definitions.Def_mme_kron_pow_mode_word_basis
import Definitions.Def_mme_basis_z_allowed_projection
import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_degeneration

/-!
DWZ Definitions 3.7, 3.9, and 8.1: exact rational prescribed Z-split powers
and finite-witness lower certificates in the normalization of Equation (3).

Only compatible lengths D*m are used. This file does not identify a real
limsup with these predicates, prove independence of denominator presentation,
or replace the paper's degeneration witnesses by restriction witnesses.
-/

set_option autoImplicit false
set_option warningAsError true

universe u

namespace MME.DWZRestrictedValue

open BigOperators Module DWZComponentRestriction

/-- An exact rational split profile, with an explicitly positive common denominator. -/
structure IntegerZSplitProfile (t : ℕ) where
  denominator : ℕ
  denominator_pos : 0 < denominator
  count : Fin t → ℕ
  count_sum : ∑ a, count a = denominator

def IntegerZSplitProfile.length {t : ℕ} (p : IntegerZSplitProfile t) (m : ℕ) : ℕ :=
  p.denominator * m

def IntegerZSplitProfile.frequency {t : ℕ} (p : IntegerZSplitProfile t)
    (a : Fin t) : ℚ :=
  (p.count a : ℚ) / p.denominator

/-- The left fine-grade count in a canonical Z-word of a tensor power.
Only the left half of each coarse factor is counted, as in Definition 3.7. -/
def leftGradeCount {ι : Type u} {t n : ℕ} (grade : ι → Fin t)
    (w : PowIndex ι n) (a : Fin t) : ℕ :=
  (Finset.univ.filter (fun r : Fin n ↦ grade (PowIndex.get n w r) = a)).card

def prescribedZWord {ι : Type u} {t : ℕ} (grade : ι → Fin t)
    (p : IntegerZSplitProfile t) (m : ℕ) (w : PowIndex ι (p.length m)) : Prop :=
  ∀ a : Fin t, leftGradeCount grade w a = p.count a * m

/-- A single Z-only coordinate projection of T^(D*m), not a sum of copies.
For a CW component, bZ must be its canonical coarse-block basis and grade
must be the left coordinate of the next finer partition. -/
noncomputable def prescribedZPower
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u} {t : ℕ}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin t)
    (p : IntegerZSplitProfile t) (m : ℕ) : TensorObj K 3 := by
  classical
  exact (T.kronPow (p.length m)).basisZAllowedSubtensor
    (kronPowModeBasis T 2 bZ (p.length m)) (prescribedZWord grade p m)

/-- A finite MM extraction from the six-symmetrization, with relation R
explicitly specified. The exponent counts all six symmetrized factors. -/
def SixFiniteWitness
    {K : Type u} [Field K]
    (R : TensorObj K 3 → TensorObj K 3 → Prop)
    (A : TensorObj K 3) (n : ℕ) (tau v : ℝ) : Prop :=
  ∃ (k : ℕ) (a b c : Fin k → ℕ),
    R (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
      (sixSymmetrization A) ∧
    v ^ (6 * n) ≤ ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)

/-- Every positive strict lower base has actual finite witnesses at
arbitrarily large compatible indices. This is the witness form of an
Equation-(3) limsup lower certificate; it does not assume an eventual
exact-frequency condition for irrational distributions. -/
def HasSixSequenceRate
    {K : Type u} [Field K]
    (R : TensorObj K 3 → TensorObj K 3 → Prop)
    (A : ℕ → TensorObj K 3) (length : ℕ → ℕ) (tau V : ℝ) : Prop :=
  0 ≤ V ∧ ∀ v : ℝ, 0 < v → v < V →
    ∀ cutoff : ℕ, ∃ m : ℕ, cutoff ≤ m ∧ cutoff ≤ length m ∧
      SixFiniteWitness R (A m) (length m) tau v

/-- Source-facing degeneration certificate for a fixed rational Z profile. -/
def HasPrescribedZSixValueAtLeast
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u} {t : ℕ}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin t)
    (p : IntegerZSplitProfile t) (tau V : ℝ) : Prop :=
  HasSixSequenceRate Degenerates (prescribedZPower T bZ grade p) p.length tau V

/-- A stronger concrete restriction certificate, kept distinct from degenerations. -/
def HasPrescribedZSixRestrictionValueAtLeast
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u} {t : ℕ}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin t)
    (p : IntegerZSplitProfile t) (tau V : ℝ) : Prop :=
  HasSixSequenceRate TensorObj.Restrict (prescribedZPower T bZ grade p) p.length tau V

/-- Definition-8.1-style pair: the value is certified for this very profile. -/
structure CertifiedValuePair
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u} {t : ℕ}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin t) (tau : ℝ) where
  profile : IntegerZSplitProfile t
  value : ℝ
  certificate : HasPrescribedZSixValueAtLeast T bZ grade profile tau value

end MME.DWZRestrictedValue


