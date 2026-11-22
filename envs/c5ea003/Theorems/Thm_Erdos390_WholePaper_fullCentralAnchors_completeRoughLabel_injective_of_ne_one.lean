-- Prove2me | Theorems.Thm_Erdos390_WholePaper_fullCentralAnchors_completeRoughLabel_injective_of_ne_one
-- name    : Erdos390.WholePaper.fullCentralAnchors_completeRoughLabel_injective_of_ne_one
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:07:15.55815+00:00
-- url     : https://prove2.me/theorems/a2e1fb01-b33f-4a39-8f34-309000580936
-- title:
--   Injectivity of nontrivial rough labels on central anchors
-- statement:
--   Let $n$ exceed the central-anchor cutoff threshold for depth $d$, and let $2\le y<\kappa_d(n)$, where $\kappa_d(n)$ is the large-marker cutoff. Take a valid large central cofactor choice $q$ and anchors $a,b$ in its full central-anchor set. Writing $R_y(a)$ for the complete rough label, one has
--   $$R_y(a)\ne1\ \text{ and }\ R_y(a)=R_y(b)\quad\Longrightarrow\quad a=b.$$
--   Thus every nontrivial complete rough label contains at most one central anchor.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalGuardCapacityReduction.lean#L59-L177

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006

theorem Erdos390.WholePaper.fullCentralAnchors_completeRoughLabel_injective_of_ne_one :
∀ {depth n y : Nat} {q : Nat → Nat},
  LE.le.{0} (Erdos390.WholePaper.centralAnchorCutoffThreshold depth) n →
    LE.le.{0} (2 : Nat) y →
      LT.lt.{0} y (Erdos390.WholePaper.centralAnchorCutoff depth n) →
        Erdos390.WholePaper.IsLargeCentralCofactorChoice n (Erdos390.WholePaper.centralAnchorCutoff depth n) q →
          ∀ {a b : Nat},
            Membership.mem.{0, 0}
                (Erdos390.WholePaper.fullCentralAnchors n (Erdos390.WholePaper.centralAnchorCutoff depth n) q) a →
              Membership.mem.{0, 0}
                  (Erdos390.WholePaper.fullCentralAnchors n (Erdos390.WholePaper.centralAnchorCutoff depth n) q) b →
                Ne.{1} (Erdos390.WholePaper.completeRoughLabel y a) (1 : Nat) →
                  Eq.{1} (Erdos390.WholePaper.completeRoughLabel y a) (Erdos390.WholePaper.completeRoughLabel y b) →
                    Eq.{1} a b := by sorry
