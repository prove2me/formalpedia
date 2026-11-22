-- Prove2me | solution 1 for Erdos390.Full.PaperBridgeFit.BridgeData.actual_fullSquarefree_weightedRow_le_of_reference
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T15:15:55.740707+00:00
-- url     : https://prove2.me/submissions/24bcb38c-37c4-4e14-9252-2d86703a46f2

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

/- Source module: Erdos390.Full.PaperActualPrimePowerRowTransfer -/
section


/-!
# Actual prime-power transfer from a reference row

The canonical raw Lemma 7.5 certificate is proved for an unguarded reference
law, whereas Lemma 8.6 uses the genuinely guarded and physically tilted law.
This file records the exact finite triangle needed to pass between them.

Only the weighted `VV-II` row is used.  This is deliberate: the compensated
slow coefficient contains the within-band deviation and therefore is not a
lift of a band vector.  A sharp band-operator estimate alone does not control
that coefficient.  The row below does, without postulating a full
`PrimePowerTransferBounds` package for the actual law.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerLemma75 PaperPrimePowerRelativeQuadratic
open PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- If a reference law satisfies Lemma 7.5 and the actual/reference
power-correction rows are small, then the actual `VV-II` row is small.  The
statement is on the literal prime subtype, so it can be used both in the
slow quadratic and in marked-prime estimates. -/
theorem actual_fullSquarefree_weightedRow_le_of_reference
    [Nonempty Head]
    {OmegaRef : Type*} [Fintype OmegaRef] {MRef : ℕ}
    (xi : B.ParamSpace)
    (referenceLaw : BoundedValuationLaw OmegaRef MRef)
    {Cpow epsilon rhoPower : ℝ}
    (h75 : PrimePowerTransferBounds referenceLaw
      B.sampleData.n B.sampleData.W Cpow epsilon)
    (hpower : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.actualValuationLaw xi).covVV p.1 q.1 -
              (B.actualValuationLaw xi).covII p.1 q.1) -
            (referenceLaw.covVV p.1 q.1 -
              referenceLaw.covII p.1 q.1)| ≤ rhoPower) :
    ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 q.1 -
            (B.actualValuationLaw xi).covII p.1 q.1| ≤
        Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon + rhoPower := by
  intro p
  have href :
      (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |referenceLaw.covVV p.1 q.1 -
            referenceLaw.covII p.1 q.1| ≤
        Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon := by
    have hrefNat := h75.row p.1 p.2
    have hattach := Finset.sum_attach
      (primeBand B.sampleData.n B.sampleData.W)
      (fun q ↦ |referenceLaw.covVV p.1 q -
        referenceLaw.covII p.1 q|)
    rw [← hattach] at hrefNat
    change (p.1 : ℝ) *
      (∑ q ∈ (primeBand B.sampleData.n B.sampleData.W).attach,
        |referenceLaw.covVV p.1 q.1 - referenceLaw.covII p.1 q.1|) ≤
      Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon at hrefNat
    simpa only using hrefNat
  have hpoint (q : BandPrime B.sampleData.n B.sampleData.W) :
      |(B.actualValuationLaw xi).covVV p.1 q.1 -
          (B.actualValuationLaw xi).covII p.1 q.1| ≤
        |((B.actualValuationLaw xi).covVV p.1 q.1 -
            (B.actualValuationLaw xi).covII p.1 q.1) -
          (referenceLaw.covVV p.1 q.1 -
            referenceLaw.covII p.1 q.1)| +
        |referenceLaw.covVV p.1 q.1 -
          referenceLaw.covII p.1 q.1| := by
    let a := (B.actualValuationLaw xi).covVV p.1 q.1 -
      (B.actualValuationLaw xi).covII p.1 q.1
    let b := referenceLaw.covVV p.1 q.1 -
      referenceLaw.covII p.1 q.1
    change |a| ≤ |a - b| + |b|
    calc
      |a| = |(a - b) + b| := by congr 1; ring
      _ ≤ |a - b| + |b| := abs_add_le (a - b : ℝ) b
  have hsum :
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 q.1 -
            (B.actualValuationLaw xi).covII p.1 q.1| ≤
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.actualValuationLaw xi).covVV p.1 q.1 -
              (B.actualValuationLaw xi).covII p.1 q.1) -
            (referenceLaw.covVV p.1 q.1 -
              referenceLaw.covII p.1 q.1)|) +
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |referenceLaw.covVV p.1 q.1 -
            referenceLaw.covII p.1 q.1| := by
    calc
      _ ≤ ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (|((B.actualValuationLaw xi).covVV p.1 q.1 -
              (B.actualValuationLaw xi).covII p.1 q.1) -
            (referenceLaw.covVV p.1 q.1 -
              referenceLaw.covII p.1 q.1)| +
          |referenceLaw.covVV p.1 q.1 -
            referenceLaw.covII p.1 q.1|) :=
        Finset.sum_le_sum fun q _hq ↦ hpoint q
      _ = _ := Finset.sum_add_distrib
  have hp0 : 0 ≤ (p.1 : ℝ) := by positivity
  calc
    (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 q.1 -
            (B.actualValuationLaw xi).covII p.1 q.1| ≤
      (p.1 : ℝ) *
        ((∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.actualValuationLaw xi).covVV p.1 q.1 -
              (B.actualValuationLaw xi).covII p.1 q.1) -
            (referenceLaw.covVV p.1 q.1 -
              referenceLaw.covII p.1 q.1)|) +
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |referenceLaw.covVV p.1 q.1 -
            referenceLaw.covII p.1 q.1|) :=
        mul_le_mul_of_nonneg_left hsum hp0
    _ = (p.1 : ℝ) *
          (∑ q : BandPrime B.sampleData.n B.sampleData.W,
            |((B.actualValuationLaw xi).covVV p.1 q.1 -
                (B.actualValuationLaw xi).covII p.1 q.1) -
              (referenceLaw.covVV p.1 q.1 -
                referenceLaw.covII p.1 q.1)|) +
        (p.1 : ℝ) *
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            |referenceLaw.covVV p.1 q.1 -
              referenceLaw.covII p.1 q.1| := by ring
    _ ≤ rhoPower +
        (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon) :=
      add_le_add (hpower p) href
    _ = Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon +
        rhoPower := by ring





end BridgeData

end

end Erdos390.Full.PaperBridgeFit

end

universe u_1 u_2 u_3
theorem solution :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band]
  (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band) [inst_4 : Nonempty.{u_1 + 1} Head]
  {OmegaRef : Type u_3} [inst_5 : Fintype.{u_3} OmegaRef] {MRef : Nat}
  (xi : Erdos390.Full.PaperBridgeFit.BridgeData.ParamSpace.{u_1, u_2} B)
  (referenceLaw : Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.{u_3} OmegaRef MRef)
  {Cpow epsilon rhoPower : Real},
  Erdos390.Full.PaperPrimePowerLemma75.PrimePowerTransferBounds.{u_3} referenceLaw
      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
      Cpow epsilon →
    (∀
        (p :
          Erdos390.Full.ArithmeticBandGeometry.BandPrime
            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
        LE.le.{0}
          (HMul.hMul.{0, 0, 0} (↑↑p)
            (∑ q :
              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
              abs.{0}
                (HSub.hSub.{0, 0, 0}
                  (HSub.hSub.{0, 0, 0}
                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi) ↑p ↑q)
                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi) ↑p ↑q))
                  (HSub.hSub.{0, 0, 0}
                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_3} referenceLaw ↑p ↑q)
                    (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_3} referenceLaw ↑p ↑q)))))
          rhoPower) →
      ∀
        (p :
          Erdos390.Full.ArithmeticBandGeometry.BandPrime
            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
            (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
              (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))),
        LE.le.{0}
          (HMul.hMul.{0, 0, 0} (↑↑p)
            (∑ q :
              Erdos390.Full.ArithmeticBandGeometry.BandPrime
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
                (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                  (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B)),
              abs.{0}
                (HSub.hSub.{0, 0, 0}
                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covVV.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi) ↑p ↑q)
                  (Erdos390.Full.PrimePowerCovariance.BoundedValuationLaw.covII.{u_1}
                    (Erdos390.Full.PaperBridgeFit.BridgeData.actualValuationLaw.{u_1, u_2} B xi) ↑p ↑q))))
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0}
              (HMul.hMul.{0, 0, 0} Cpow
                (HDiv.hDiv.{0, 0, 0} (1 : Real)
                  ↑(Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                      (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))))
              epsilon)
            rhoPower) := by
  exact @Erdos390.Full.PaperBridgeFit.BridgeData.actual_fullSquarefree_weightedRow_le_of_reference
