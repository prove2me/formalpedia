-- Prove2me | Definitions.Def_mme_CW_q6_paired_cyclic_induced
-- name    : mme_CW_q6_paired_cyclic_induced
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T12:17:02.632016+00:00
-- url     : https://prove2.me/theorems/e6bde8a6-8898-4fac-827d-23fecfdbece0
-- title:
--   Paired cyclic support, inducedness, and its finite conflict graph
-- statement:
--   For a primary q=6 coupled-address family equipped with one common balanced halving, define when a mixed triple of retained entries survives both oppositely cyclically oriented halves. In physical mode order (p0,p1,p2), the first half reads the original coupled coordinates as (X,Y,Z)=(p2,p0,p1), while the second reads them as (p1,p2,p0). The family is paired-cyclic-induced when every such simultaneously supported mixed triple is fully diagonal: p0=p1=p2. The module also defines the exact finite conflict graph, namely the two-section of the hypergraph of non-diagonal supported triples. This is the weakest direct off-support hypothesis for the exact paired 121/211 projector construction; ordinary primary-family inducedness alone does not imply it.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), induced-family pruning; Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3/Table 2. The paired cyclic predicate is the exact mixed-support condition obtained by composing the twice- and once-cyclic orientations of the 121/211 factors.

import Definitions.Def_mme_CW_q6_common_paired_halving
import Mathlib.Combinatorics.SimpleGraph.Basic

open MME

universe u

set_option autoImplicit false

namespace MME

/-- Local support of one coarse grade triple in the four-sum coupled
constituent. -/
def CWQ6CoupledLocalSupported (x y z : Fin 3) : Prop :=
  (x = 0 ∧ y = 0 ∧ z = 0) ∨
  (x = 1 ∧ y = 1 ∧ z = 1) ∨
  (x = 0 ∧ y = 1 ∧ z = 2) ∨
  (x = 1 ∧ y = 0 ∧ z = 2)

/-- A cyclic mixed triple which survives simultaneously in the two
oriented halves.  Physical mode choices are ordered as `(p0,p1,p2)`.
In the twice-cyclic first factor they become the original coupled choices
`(X,Y,Z) = (p2,p0,p1)`; in the once-cyclic second factor they become
`(X,Y,Z) = (p1,p2,p0)`. -/
def CWQ6PrimaryHashFamily.PairedCyclicSupported
    {N L G A H : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (p0 p1 p2 : Fin A × Fin H) : Prop :=
  (∀ r : Fin N,
    CWQ6CoupledLocalSupported
      ((family.entry p2).val 0 (halving.position (Sum.inl r)))
      ((family.entry p0).val 1 (halving.position (Sum.inl r)))
      ((family.entry p1).val 2 (halving.position (Sum.inl r)))) ∧
  (∀ r : Fin N,
    CWQ6CoupledLocalSupported
      ((family.entry p1).val 0 (halving.position (Sum.inr r)))
      ((family.entry p2).val 1 (halving.position (Sum.inr r)))
      ((family.entry p0).val 2 (halving.position (Sum.inr r))))

/-- The exact additional inducedness property required by the paired
121/211 projector construction: every cyclic mixed choice which is supported
in both oriented halves is the diagonal choice. -/
def CWQ6PrimaryHashFamily.PairedCyclicInduced
    {N L G A H : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) : Prop :=
  ∀ p0 p1 p2 : Fin A × Fin H,
    family.PairedCyclicSupported halving p0 p1 p2 →
      p0 = p1 ∧ p1 = p2

/-- Membership of an entry in a three-entry cyclic mixed choice. -/
def CWQ6PrimaryHashFamily.InPairedTriple
    {N L G A H : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (p : Fin A × Fin H) (p0 p1 p2 : Fin A × Fin H) : Prop :=
  p = p0 ∨ p = p1 ∨ p = p2

/-- The finite conflict graph (the two-section of the bad cyclic-triple
hypergraph).  Two distinct retained entries are adjacent exactly when they
co-occur in some non-diagonal paired cyclic supported triple. -/
def CWQ6PrimaryHashFamily.pairedCyclicConflictGraph
    {N L G A H : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) :
    SimpleGraph (Fin A × Fin H) :=
  SimpleGraph.fromRel (fun p q ↦
    ∃ p0 p1 p2 : Fin A × Fin H,
      family.PairedCyclicSupported halving p0 p1 p2 ∧
      ¬ (p0 = p1 ∧ p1 = p2) ∧
      family.InPairedTriple p p0 p1 p2 ∧
      family.InPairedTriple q p0 p1 p2)

end MME


