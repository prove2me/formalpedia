-- Prove2me | Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_canonicalNonstepLocalDiagonalCutoff_eventually
-- name    : Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalNonstepLocalDiagonalCutoff_eventually
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:24:48.942601+00:00
-- url     : https://prove2.me/theorems/d4a41d9b-fc2f-425a-b34c-abbaa7e6de18
-- title:
--   Vanishing local deviation diagonal at the canonical band center scale
-- statement:
--   Fix a relative mesh M with δ>0 and W at least canonicalNonstepLocalDiagonalCutoff. For every r>0, eventually in n, every choice of n>1, W≠0, scale separation and band i in the canonical partition P satisfies the bound below. This includes the moving low band and preserves the actual mesh ratio.
--
--   $$D_i\le r(\delta+M.\mathrm{ratio})\alpha_i.$$
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperCanonicalNonstepLocalDiagonalEventually.lean#L44-L250

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002
import Definitions.Def_erdos390_analytic_foundations_003
import Definitions.Def_erdos390_analytic_foundations_004
import Definitions.Def_erdos390_analytic_foundations_005

theorem Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalNonstepLocalDiagonalCutoff_eventually :
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) (hdelta : LT.lt.{0} (0 : Real) delta)
  (W : Nat),
  LE.le.{0} Erdos390.Full.RegularMeshPrimeCutoffs.canonicalNonstepLocalDiagonalCutoff W →
    ∀ {r : Real},
      LT.lt.{0} (0 : Real) r →
        ∀ᶠ (n : Nat) in Filter.atTop.{0},
          ∀ (hn : LT.lt.{0} (1 : Nat) n) (hWne : Ne.{1} W (0 : Nat))
            (S : Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M n W)
            (i : Fin (HAdd.hAdd.{0, 0, 0} (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M) (1 : Nat))),
            have P := Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta hn hWne S;
            LE.le.{0} (Erdos390.Full.ArithmeticBandGeometry.Partition.normalizedDeviationReciprocalSquare.{0} P i)
              (HMul.hMul.{0, 0, 0}
                (HMul.hMul.{0, 0, 0} r (HAdd.hAdd.{0, 0, 0} delta (Erdos390.Full.RegularRelativeMesh.Mesh.ratio M)))
                (Erdos390.Full.ArithmeticBandGeometry.Partition.center.{0} P i)) := by sorry
