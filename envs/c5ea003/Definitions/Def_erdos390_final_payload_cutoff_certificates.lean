-- Prove2me | Definitions.Def_erdos390_final_payload_cutoff_certificates
-- name    : erdos390_final_payload_cutoff_certificates
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T16:07:49.657407+00:00
-- url     : https://prove2.me/theorems/dfedf0f3-22e0-4781-abb0-4be02fd59788
-- title:
--   Nonzero cutoff certificates for the final divisor payload
-- statement:
--   These two closed arithmetic lemmas state that the sample cutoff W cannot be zero when W is at least two. Their explicit parameters retain the mesh and guarded-anchor data used by the final divisor payload; no additional assumption is introduced.
-- source:
--   https://github.com/ShouqiaoW/erdos/tree/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean

import Definitions.Def_erdos390_analytic_foundations_010

theorem Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack._proof_1 :
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) {P : Finset.{0} Nat}
  (B :
    Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
      (Erdos390.WholePaper.BankPaperCanonicalExponentBand M)),
  LE.le.{0} 2
      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0}
        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)) →
    Eq.{1}
        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0}
          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B))
        0 →
      False := by intros; omega

theorem Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack._proof_2 :
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) {P : Finset.{0} Nat}
  (B :
    Erdos390.Full.PaperBridgeFit.BridgeData.{0, 0} (Erdos390.Full.PaperHeadSimplex.Tag P)
      (Erdos390.WholePaper.BankPaperCanonicalExponentBand M))
  {c : Real} {depth : Nat} {K0 : Nat}
  (R :
    Erdos390.WholePaper.BankPaperRealization
      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B))
      (Erdos390.WholePaper.upperEndpoint
        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B))
        (Erdos390.WholePaper.upperTailLength c
          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)))))
  (certificate :
    Erdos390.WholePaper.GuardedCentralAnchorCertificate c depth
      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.n.{0}
        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B))
      (Erdos390.WholePaper.BankPaperRealization.anchorGuardLeftCore R)
      (Erdos390.WholePaper.BankPaperRealization.anchorGuardRightCore R)
      (Erdos390.WholePaper.BankPaperRealization.centralChangedMarkers R depth))
  (deltaStar : Real),
  LE.le.{0} 2
      (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0}
        (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B)) →
    Eq.{1}
        (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{0}
          (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{0, 0} B))
        0 →
      False := by intros; omega


