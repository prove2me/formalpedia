-- Prove2me | Theorems.Thm_Erdos390_Full_RegularMeshPrimeCutoffs_Mesh_canonicalPrimeAnchorCutoff_eventually
-- name    : Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff_eventually
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:25:29.408885+00:00
-- url     : https://prove2.me/theorems/9cb8dd61-8186-4b9f-927f-06c85f1ae401
-- title:
--   Canonical prime anchors have interior support and positive mass
-- statement:
--   Fix a regular relative mesh $M$ with $\delta>0$ and $W\ge\mathrm{canonicalPrimeAnchorCutoff}$. Let a nonempty set $A$ of positive cells satisfy $\epsilon<M.\operatorname{lower}(k)$ and $M.\operatorname{upper}(k)\le1-\epsilon$ for $k\in A$, and $\frac12\sum_{k\in A}M.\operatorname{width}(k)\ge1/8$. Eventually $n>1,W\ne0$, and for every scale-separation certificate, the canonical union of anchor primes satisfies
--
--   $$t_p\in[\epsilon,1-\epsilon]\ (p\in\mathrm{anchor}),\qquad\mathrm{anchorMass}(\mathrm{primeWeight},\mathrm{anchor})\ge\frac18.$$
--
--   This constructs literal arithmetic anchors with a cutoff chosen before the mesh.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperCanonicalPrimeAnchorEventually.lean#L245-L370

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

theorem Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff_eventually :
∀ {delta eta : Real} (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta) (hdelta : LT.lt.{0} (0 : Real) delta)
  (W : Nat),
  LE.le.{0} Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff W →
    ∀ {epsilon : Real} (anchors : Finset.{0} (Fin (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M))),
      Finset.Nonempty.{0} anchors →
        (∀ (k : Fin (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M)),
            Membership.mem.{0, 0} anchors k → LT.lt.{0} epsilon (Erdos390.Full.RegularRelativeMesh.Mesh.lower M k)) →
          (∀ (k : Fin (Erdos390.Full.RegularRelativeMesh.Mesh.cellCount M)),
              Membership.mem.{0, 0} anchors k →
                LE.le.{0} (Erdos390.Full.RegularRelativeMesh.Mesh.upper M k) (HSub.hSub.{0, 0, 0} (1 : Real) epsilon)) →
            LE.le.{0} (1 / 8 : Real)
                (HDiv.hDiv.{0, 0, 0} (∑ k ∈ anchors, Erdos390.Full.RegularRelativeMesh.Mesh.width M k) (2 : Real)) →
              ∀ᶠ (n : Nat) in Filter.atTop.{0},
                ∃ (hWne : Ne.{1} W (0 : Nat)) (hn : LT.lt.{0} (1 : Nat) n),
                  ∀ (S : Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M n W),
                    have P := Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta hn hWne S;
                    have anchor := Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorSet M P anchors;
                    And
                      (∀ (p : Erdos390.Full.ArithmeticBandGeometry.BandPrime n W),
                        Membership.mem.{0, 0} anchor p →
                          Membership.mem.{0, 0} (Set.Icc.{0} epsilon (HSub.hSub.{0, 0, 0} (1 : Real) epsilon))
                            (Erdos390.Full.ArithmeticModel.tPrime n ↑p))
                      (LE.le.{0} (1 / 8 : Real)
                        (Erdos390.Full.FiniteAnchoredDirichletQuadratic.anchorMass.{0}
                          (Erdos390.Full.PrimeSquarefreeDirichletGeometry.primeWeight n) anchor)) := by sorry
