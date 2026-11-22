-- Prove2me | Definitions.Def_erdos390_analytic_statement_auxiliaries
-- name    : erdos390_analytic_statement_auxiliaries
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T15:20:52.386715+00:00
-- url     : https://prove2.me/theorems/26ed3f39-bd21-4c62-950a-9815f22f6f3f
-- title:
--   Arithmetic certificates for positive prime cutoffs
-- statement:
--   These two elementary arithmetic certificates make explicit the cutoff facts used inside dependent analytic statements. For a natural cutoff $W$,
--
--   $$W\ge2\;\Longrightarrow\; W
--   e0.$$
--
--   If $B$ is finite bridge data with recorded cutoff $W_B=W$ and $W>1$, then
--
--   $$W_B>1.$$
--
--   Equivalently, the hypotheses $W>1$, $W_B=W$ and $
--   eg(W_B>1)$ are inconsistent. The finite index types and their enumeration/equality instances are arbitrary. Both certificates are proved by elementary natural-number arithmetic and supply proof arguments in the selected-mesh Schur and ratio-cell statements.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperSelectedMeshSchurEventually.lean#L39-L140 ; https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalRatioCellMomentTraffic.lean#L393-L420

import Mathlib
import Definitions.Def_erdos390_analytic_foundations_002

universe u_1 u_2

theorem Erdos390.Full.PaperBridgeFit.BridgeData.eventually_exists_uniform_actualBandSchurEquiv_and_quadratic._proof_1 :
∀ {Head : Type u_1} {Band : Type u_2} [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
  [inst_2 : Fintype.{u_2} Band] [inst_3 : DecidableEq.{u_2 + 1} Band] (W : Nat),
  LT.lt.{0} (1 : Nat) W →
    ∀ (n : Nat) (B : Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, u_2} Head Band),
      Eq.{1}
          (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
            (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))
          W →
        Not
            (LT.lt.{0} (1 : Nat)
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, u_2} B))) →
          False := by
  intros
  omega

theorem Erdos390.WholePaper.bankPaperCanonical_low_shiftedCoordinate_le._proof_1 :
∀ {n : Nat} {W : Nat}, LE.le.{0} (2 : Nat) W → Eq.{1} W (0 : Nat) → False := by
  intros
  omega


