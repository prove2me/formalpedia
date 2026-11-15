-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.minor_natAbs_le_exceptionalPrimeBound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:19:11.742677+00:00
-- url     : https://prove2.me/submissions/ebbe088f-4426-4fc6-aba0-cdaa38142c99

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Explicit exceptional moduli for integer affine forms

The local-factor argument needs a finite bound after which every selected
nonzero coefficient and every selected nonzero two-by-two minor remains
nonzero modulo `p`.  We use a deliberately coarse sum of absolute values;
its advantage is that it is total, explicit, and requires no choices.
-/
open Wikipedia.SzemeredisTheorem

open Wikipedia.SzemeredisTheorem in
theorem solution
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (forms : κ → AffineForm ι ℤ)
    (q r : κ) (i j : ι) :
    Int.natAbs
        ((forms q).coefficientMinor (forms r) i j) ≤
      exceptionalPrimeBound forms := by
  have hj :
      Int.natAbs
          ((forms q).coefficientMinor (forms r) i j) ≤
        ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r) i j') :=
    Finset.single_le_sum
      (f := fun j' : ι =>
        Int.natAbs
          ((forms q).coefficientMinor (forms r) i j'))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hi :
      (∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r) i j')) ≤
        ∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r) i' j') :=
    Finset.single_le_sum
      (f := fun i' : ι =>
        ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r) i' j'))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hr :
      (∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r) i' j')) ≤
        ∑ r' : κ, ∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r') i' j') :=
    Finset.single_le_sum
      (f := fun r' : κ =>
        ∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r') i' j'))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  have hq :
      (∑ r' : κ, ∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r') i' j')) ≤
        ∑ q' : κ, ∑ r' : κ, ∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q').coefficientMinor (forms r') i' j') :=
    Finset.single_le_sum
      (f := fun q' : κ =>
        ∑ r' : κ, ∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q').coefficientMinor (forms r') i' j'))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
  exact (hj.trans (hi.trans (hr.trans hq))).trans
    (Nat.le_add_left _ _)
