-- Prove2me | Definitions.Def_erdos390_analytic_nonstep_certificate
-- name    : erdos390_analytic_nonstep_certificate
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-17T15:58:15.009871+00:00
-- url     : https://prove2.me/theorems/38eef3c6-cc50-4fdb-8f37-a5ae0d6f9a67
-- title:
--   Positive cutoff certificate for the nonstep residual row
-- statement:
--   If a cutoff is at least two and W is at least that cutoff, then W is greater than one. This closed arithmetic certificate supplies a named proof argument for the nonstep residual-row proposition.
-- source:
--   https://github.com/ShouqiaoW/erdos/tree/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean

import Definitions.Def_erdos390_analytic_foundations_007

universe u_1
theorem Erdos390.Full.PaperBridgeFit.BridgeData.exists_global_cutoff_eventually_canonical_nonstepSlowResidualRow_le._proof_1 :
∀ (W₀ : Nat),
  LE.le.{0} 2 W₀ →
    ∀ (W : Nat),
      LE.le.{0} W₀ W →
        ∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) {Head : Type u_1}
          [inst : Fintype.{u_1} Head] [inst_1 : DecidableEq.{u_1 + 1} Head]
          (I : Erdos390.Full.PaperGuardCensus.PhysicalIntervals) (n : Nat)
          (B :
            Erdos390.Full.PaperBridgeFit.BridgeData.{u_1, 0} Head
              (Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) 1))),
          Eq.{1}
              (Erdos390.Full.PaperBridgeFit.StructuredSampleData.W.{u_1}
                (Erdos390.Full.PaperBridgeFit.BridgeData.sampleData.{u_1, 0} B))
              W →
            Not (LT.lt.{0} 1 W) → False := by intros; omega


