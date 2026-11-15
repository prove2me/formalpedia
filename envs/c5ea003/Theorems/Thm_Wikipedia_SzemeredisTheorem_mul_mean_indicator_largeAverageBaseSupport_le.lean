-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_mul_mean_indicator_largeAverageBaseSupport_le
-- name    : Wikipedia.SzemeredisTheorem.mul_mean_indicator_largeAverageBaseSupport_le
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:15:49.950199+00:00
-- url     : https://prove2.me/theorems/d241e135-5e8f-415c-8290-5d7aa3e6e52c
-- title:
--   Markov inequality for partition-atom averages
-- statement:
--   Let $\Omega$ be finite, let $P$ be a face partition, and let $f:\Omega\to\mathbb R$ be nonnegative. For $\beta\ge0$, let $S$ be the large-average base support, consisting of points whose partition-conditional mean is strictly greater than $\beta$. Then
--   $$
--   \beta\,\mathbb E_x1_S(x)\le\mathbb E_xf(x).
--   $$
--   This is a finite Markov bound on the conditional averages of genuine partition atoms; it includes $\beta=0$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedGoodAtoms.lean#L385-L408

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Unweighted
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Good ordered atoms and localized bad-base accounting

The hypergraph removal argument must localize a global coarse--fine energy
gap to genuine boundary atoms.  This file supplies the finite bookkeeping
for that step.

For an arbitrary finite partition we define the union of a selected family
of atoms and prove that its normalized mass is the sum of the atom masses.
Sublevel atoms charge only a small part of a target atom, while atoms on
which a nonnegative local average is large satisfy a finite Markov bound.
Applying this to the square of a coarse--fine conditional-density defect
gives the headline estimate

```text
mass (upperAtom ∩ badBase) ≤
  densityThreshold + atomEnergyGap / defectThreshold.
```

The final section specializes these definitions to shared ordered
boundaries and packages realizable closed atom configurations.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Canonical atoms and unions of genuine partition atoms -/
/-! ## Sublevel atoms and low-density charging -/
/-! ## Large local averages and finite Markov bounds -/

theorem Wikipedia.SzemeredisTheorem.mul_mean_indicator_largeAverageBaseSupport_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FacePartition Ω) (f : Ω → ℝ)
    (hf : ∀ x, 0 ≤ f x)
    {β : ℝ} (_hβ : 0 ≤ β) :
    β * mean (finsetIndicator
        (largeAverageBaseSupport P f β)) ≤
      mean f := by sorry
