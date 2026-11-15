-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.mean_insertNth
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:14:54.459429+00:00
-- url     : https://prove2.me/submissions/2797eb9e-1b10-41a6-bde9-00e6d8e133ba

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Cut control of arithmetic-progression simplex counts

For one edge in the arithmetic-progression simplex, the remaining edge
weights form a product of deleted-coordinate cut tests.  The distinguished
edge is an automorphic weighted sum when the modulus is coprime to the
relevant factorial.  This file makes that reduction exact and then applies
cut discrepancy edge by edge.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- A normalized average over a tuple can be computed by first fixing one
coordinate and then averaging the remaining tuple. -/
theorem solution
    {G : Type*} [Fintype G] (n : ℕ)
    (j : Fin (n + 1)) (F : (Fin (n + 1) → G) → ℝ) :
    mean F =
      mean₂ (fun a : G => fun y : Fin n → G =>
        F (Fin.insertNth j a y)) := by
  calc
    mean F =
        mean (fun p : G × (Fin n → G) =>
          F (Fin.insertNth j p.1 p.2)) := by
      unfold mean
      apply Fintype.expect_equiv
        (Fin.insertNthEquiv (fun _ : Fin (n + 1) => G) j).symm
      intro x
      congr 1
      simp
    _ = mean₂ (fun a : G => fun y : Fin n → G =>
          F (Fin.insertNth j a y)) := by
      simpa [mean, mean₂] using
        (Finset.expect_product
          (Finset.univ : Finset G)
          (Finset.univ : Finset (Fin n → G))
          (fun p : G × (Fin n → G) =>
            F (Fin.insertNth j p.1 p.2)))
