-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:51:20.417725+00:00
-- url     : https://prove2.me/theorems/4a1915d9-13c9-4a08-b0e4-daead98ff00d
-- title:
--   AP coefficient automorphisms and canonical deleted-face coordinates
-- statement:
--   If a natural modulus $N$ is coprime to $(k-1)!$, multiplication by the difference $i-j$ of two distinct indices below $k$ is an additive automorphism of $\mathbb Z/N\mathbb Z$.
--
--   The bundle supplies this automorphism, the increasing equivalence between $\operatorname{Fin}(n)$ and the coordinates other than a fixed $j< n+1$, and the induced conversion from an ordinary tuple to a dependent deleted-coordinate vector. The AP-face scaling family uses these maps to attach the coefficient $i-j$ to each remaining face coordinate. The factorial-coprimality hypothesis is retained explicitly.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/APCut.lean#L21-L167

import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Arithmetic-progression face forms as transported cut forms

For a fixed deleted vertex, the arithmetic-progression face form has
coefficients `i - j`.  Coprimality of the modulus with `(k-1)!` makes every
one of these coefficients a unit, so the face form is an automorphic
coordinate sum.  This file proves the coefficient and reindexing facts needed
to apply transported cut discrepancy.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Every nonzero AP coefficient is a unit modulo a modulus coprime to
`(k-1)!`. -/
theorem apCoefficient_isUnit_of_coprime_factorial
    {k N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial (k - 1)))
    (i j : Fin k) (hij : i ≠ j) :
    IsUnit (((i : ℤ) - (j : ℤ) : ℤ) : ZMod N) := by
  apply (fun h : IsCoprime (N : ℤ) ((i : ℤ) - (j : ℤ)) =>
    (ZMod.unitOfIsCoprime _ (isCoprime_comm.mp h)).isUnit)
  rw [Int.isCoprime_iff_nat_coprime]
  have hdiff :
      (i : ℤ) - (j : ℤ) ≠ 0 := by
    intro h
    apply hij
    apply Fin.ext
    exact_mod_cast sub_eq_zero.mp h
  have hpos :
      0 < Int.natAbs ((i : ℤ) - (j : ℤ)) :=
    Int.natAbs_pos.mpr hdiff
  have hle :
      Int.natAbs ((i : ℤ) - (j : ℤ)) ≤ k - 1 := by
    have hi : (i : ℕ) ≤ k - 1 := by omega
    have hj : (j : ℕ) ≤ k - 1 := by omega
    exact Int.natAbs_coe_sub_coe_le_of_le hi hj
  have hdvd :
      Int.natAbs ((i : ℤ) - (j : ℤ)) ∣
        Nat.factorial (k - 1) :=
    Nat.dvd_factorial hpos hle
  simpa using hN.coprime_dvd_right hdvd

/-- Multiplication by one AP coefficient as an additive automorphism. -/
noncomputable def apCoefficientAddEquiv
    {k N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial (k - 1)))
    (i j : Fin k) (hij : i ≠ j) :
    ZMod N ≃+ ZMod N :=
  mulAddEquivOfIsUnit
    ((((i : ℤ) - (j : ℤ) : ℤ) : ZMod N))
    (apCoefficient_isUnit_of_coprime_factorial hN i j hij)



/-- `Fin n` is canonically equivalent to the coordinates of `Fin (n+1)`
other than `j`. -/
noncomputable def finSuccAboveEquiv {n : ℕ} (j : Fin (n + 1)) :
    Fin n ≃ {i : Fin (n + 1) // i ≠ j} :=
  Equiv.ofBijective
    (fun t : Fin n => ⟨j.succAbove t, Fin.succAbove_ne j t⟩)
    ⟨by
      intro a b hab
      apply Fin.succAbove_right_injective
      exact congrArg Subtype.val hab,
    by
      intro i
      obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq i.2
      exact ⟨t, Subtype.ext ht⟩⟩



/-- Convert an ordinary `Fin n` tuple to the dependent deleted-coordinate
tuple for colour `j`. -/
noncomputable def finTupleToDeletedVector
    {n : ℕ} {G : Type*}
    (j : Fin (n + 1))
    (y : Fin n → G) :
    DeletedVector (fun _ : Fin (n + 1) => G) j :=
  fun i => y ((finSuccAboveEquiv j).symm i)

@[simp]
theorem finTupleToDeletedVector_succAbove
    {n : ℕ} {G : Type*}
    (j : Fin (n + 1))
    (y : Fin n → G)
    (t : Fin n) :
    finTupleToDeletedVector j y
        (finSuccAboveEquiv j t) =
      y t := by
  simp [finTupleToDeletedVector]







/-- The coordinate automorphisms attached to one AP face. -/
noncomputable def apFaceScalingEquiv
    {n N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial n))
    (j : Fin (n + 1)) (t : Fin n) :
    ZMod N ≃+ ZMod N :=
  apCoefficientAddEquiv
    (by simpa using hN) (j.succAbove t) j
    (Fin.succAbove_ne j t)



end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.apCoefficientAddEquiv.congr_simp,
    `Wikipedia.SzemeredisTheorem.apCoefficientAddEquiv.eq_1,
    `Wikipedia.SzemeredisTheorem.apFaceScalingEquiv.eq_1,
    `Wikipedia.SzemeredisTheorem.finTupleToDeletedVector.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


