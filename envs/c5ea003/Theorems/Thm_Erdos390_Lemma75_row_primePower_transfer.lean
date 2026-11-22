-- Prove2me | Theorems.Thm_Erdos390_Lemma75_row_primePower_transfer
-- name    : Erdos390.Lemma75.row_primePower_transfer
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T15:32:35.655965+00:00
-- url     : https://prove2.me/theorems/f669e17b-99ff-4954-91dc-be0c0c389edb
-- title:
--   Abstract weighted covariance-row transfer for prime powers
-- statement:
--   Let $\mu$ be a finite probability law and $P$ a finite index set. Let $0\le I_i\le1$, $J_i\ge0$, $J_i\le J_i^2$, and $I_iJ_i=J_i$ pointwise. Suppose $C,\epsilon\ge0$, $0\le w\le1$, $0\le t_i\le1$, $0\le u_i\le w$, and $a_i\ge0$ with $a_iu_i=1$. For distinct indices assume the bounds $$|\operatorname{Cov}(J_i,I_j)|\le(Ct_it_j+\epsilon)u_i^2u_j+r^{JI}_{ij},\quad |\operatorname{Cov}(I_i,J_j)|\le(Ct_it_j+\epsilon)u_iu_j^2+r^{IJ}_{ij},$$ $$|\operatorname{Cov}(J_i,J_j)|\le(Ct_it_j+\epsilon)u_i^2u_j^2+r^{JJ}_{ij}.$$ Assume also $\mathbb EJ_i^2\le(C+\epsilon)u_i^2+r^D_i$, $\sum_Pt_ju_j\le H_T$, $\sum_Pu_j\le H_1$, $\sum_Pu_j^2\le H_2w$, and $a_i(\sum_{j\ne i}(r^{JI}_{ij}+r^{IJ}_{ij}+r^{JJ}_{ij})+3r^D_i)\le R$ for each row.
--
--   $$a_i\sum_{j\in P}|\operatorname{Cov}(I_i+J_i,I_j+J_j)-\operatorname{Cov}(I_i,I_j)|\le C(H_T+2H_2+3)w+\epsilon(H_1+2H_2+3)w+R.$$
--
--   This is the finite probability mechanism behind the prime-power row estimate of Lemma 7.5.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Lemma75.lean#L907-L1229

import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_002

universe u_1 u_2

theorem Erdos390.Lemma75.row_primePower_transfer :
∀ {Ω : Type u_1} {ι : Type u_2} [inst : Fintype.{u_1} Ω] [inst_1 : DecidableEq.{u_2 + 1} ι]
  (μ : Erdos390.Lemma75.FiniteProbability.{u_1} Ω) (P : Finset.{u_2} ι) (I J : ι → Ω → Real) (t u rowScale : ι → Real)
  (C ε invW HT H1 H2 remRow : Real) (rJI rIJ rJJ : ι → ι → Real) (rD : ι → Real),
  LE.le.{0} (0 : Real) C →
    LE.le.{0} (0 : Real) ε →
      LE.le.{0} (0 : Real) invW →
        LE.le.{0} invW (1 : Real) →
          (∀ (i : ι), Membership.mem.{u_2, u_2} P i → LE.le.{0} (0 : Real) (t i)) →
            (∀ (i : ι), Membership.mem.{u_2, u_2} P i → LE.le.{0} (t i) (1 : Real)) →
              (∀ (i : ι), Membership.mem.{u_2, u_2} P i → LE.le.{0} (0 : Real) (u i)) →
                (∀ (i : ι), Membership.mem.{u_2, u_2} P i → LE.le.{0} (u i) invW) →
                  (∀ (i : ι), Membership.mem.{u_2, u_2} P i → LE.le.{0} (0 : Real) (rowScale i)) →
                    (∀ (i : ι),
                        Membership.mem.{u_2, u_2} P i → Eq.{1} (HMul.hMul.{0, 0, 0} (rowScale i) (u i)) (1 : Real)) →
                      (∀ (i : ι), Membership.mem.{u_2, u_2} P i → ∀ (ω : Ω), LE.le.{0} (0 : Real) (I i ω)) →
                        (∀ (i : ι), Membership.mem.{u_2, u_2} P i → ∀ (ω : Ω), LE.le.{0} (I i ω) (1 : Real)) →
                          (∀ (i : ι), Membership.mem.{u_2, u_2} P i → ∀ (ω : Ω), LE.le.{0} (0 : Real) (J i ω)) →
                            (∀ (i : ι),
                                Membership.mem.{u_2, u_2} P i →
                                  ∀ (ω : Ω), LE.le.{0} (J i ω) (HPow.hPow.{0, 0, 0} (J i ω) (2 : Nat))) →
                              (∀ (i : ι),
                                  Membership.mem.{u_2, u_2} P i →
                                    ∀ (ω : Ω), Eq.{1} (HMul.hMul.{0, 0, 0} (I i ω) (J i ω)) (J i ω)) →
                                (∀ (i : ι),
                                    Membership.mem.{u_2, u_2} P i →
                                      ∀ (j : ι),
                                        Membership.mem.{u_2, u_2} (Finset.erase.{u_2} P i) j →
                                          LE.le.{0}
                                            (abs.{0}
                                              (Erdos390.Lemma75.FiniteProbability.covariance.{u_1} μ (J i) (I j)))
                                            (HAdd.hAdd.{0, 0, 0}
                                              (HAdd.hAdd.{0, 0, 0}
                                                (HMul.hMul.{0, 0, 0}
                                                  (HMul.hMul.{0, 0, 0}
                                                    (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C (t i)) (t j))
                                                    (HPow.hPow.{0, 0, 0} (u i) (2 : Nat)))
                                                  (u j))
                                                (HMul.hMul.{0, 0, 0}
                                                  (HMul.hMul.{0, 0, 0} ε (HPow.hPow.{0, 0, 0} (u i) (2 : Nat))) (u j)))
                                              (rJI i j))) →
                                  (∀ (i : ι),
                                      Membership.mem.{u_2, u_2} P i →
                                        ∀ (j : ι),
                                          Membership.mem.{u_2, u_2} (Finset.erase.{u_2} P i) j →
                                            LE.le.{0}
                                              (abs.{0}
                                                (Erdos390.Lemma75.FiniteProbability.covariance.{u_1} μ (I i) (J j)))
                                              (HAdd.hAdd.{0, 0, 0}
                                                (HAdd.hAdd.{0, 0, 0}
                                                  (HMul.hMul.{0, 0, 0}
                                                    (HMul.hMul.{0, 0, 0}
                                                      (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C (t i)) (t j)) (u i))
                                                    (HPow.hPow.{0, 0, 0} (u j) (2 : Nat)))
                                                  (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} ε (u i))
                                                    (HPow.hPow.{0, 0, 0} (u j) (2 : Nat))))
                                                (rIJ i j))) →
                                    (∀ (i : ι),
                                        Membership.mem.{u_2, u_2} P i →
                                          ∀ (j : ι),
                                            Membership.mem.{u_2, u_2} (Finset.erase.{u_2} P i) j →
                                              LE.le.{0}
                                                (abs.{0}
                                                  (Erdos390.Lemma75.FiniteProbability.covariance.{u_1} μ (J i) (J j)))
                                                (HAdd.hAdd.{0, 0, 0}
                                                  (HAdd.hAdd.{0, 0, 0}
                                                    (HMul.hMul.{0, 0, 0}
                                                      (HMul.hMul.{0, 0, 0}
                                                        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C (t i)) (t j))
                                                        (HPow.hPow.{0, 0, 0} (u i) (2 : Nat)))
                                                      (HPow.hPow.{0, 0, 0} (u j) (2 : Nat)))
                                                    (HMul.hMul.{0, 0, 0}
                                                      (HMul.hMul.{0, 0, 0} ε (HPow.hPow.{0, 0, 0} (u i) (2 : Nat)))
                                                      (HPow.hPow.{0, 0, 0} (u j) (2 : Nat))))
                                                  (rJJ i j))) →
                                      (∀ (i : ι),
                                          Membership.mem.{u_2, u_2} P i →
                                            LE.le.{0}
                                              (Erdos390.Lemma75.FiniteProbability.expect.{u_1} μ fun ω =>
                                                HPow.hPow.{0, 0, 0} (J i ω) (2 : Nat))
                                              (HAdd.hAdd.{0, 0, 0}
                                                (HMul.hMul.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} C ε)
                                                  (HPow.hPow.{0, 0, 0} (u i) (2 : Nat)))
                                                (rD i))) →
                                        LE.le.{0} (∑ j ∈ P, HMul.hMul.{0, 0, 0} (t j) (u j)) HT →
                                          LE.le.{0} (∑ j ∈ P, u j) H1 →
                                            LE.le.{0} (∑ j ∈ P, HPow.hPow.{0, 0, 0} (u j) (2 : Nat))
                                                (HMul.hMul.{0, 0, 0} H2 invW) →
                                              (∀ (i : ι),
                                                  Membership.mem.{u_2, u_2} P i →
                                                    LE.le.{0}
                                                      (HMul.hMul.{0, 0, 0} (rowScale i)
                                                        (HAdd.hAdd.{0, 0, 0}
                                                          (∑ j ∈ Finset.erase.{u_2} P i,
                                                            HAdd.hAdd.{0, 0, 0}
                                                              (HAdd.hAdd.{0, 0, 0} (rJI i j) (rIJ i j)) (rJJ i j))
                                                          (HMul.hMul.{0, 0, 0} (3 : Real) (rD i))))
                                                      remRow) →
                                                ∀ (i : ι),
                                                  Membership.mem.{u_2, u_2} P i →
                                                    LE.le.{0}
                                                      (HMul.hMul.{0, 0, 0} (rowScale i)
                                                        (∑ j ∈ P,
                                                          abs.{0}
                                                            (HSub.hSub.{0, 0, 0}
                                                              (Erdos390.Lemma75.FiniteProbability.covariance.{u_1} μ
                                                                (fun ω => HAdd.hAdd.{0, 0, 0} (I i ω) (J i ω)) fun ω =>
                                                                HAdd.hAdd.{0, 0, 0} (I j ω) (J j ω))
                                                              (Erdos390.Lemma75.FiniteProbability.covariance.{u_1} μ
                                                                (I i) (I j)))))
                                                      (HAdd.hAdd.{0, 0, 0}
                                                        (HAdd.hAdd.{0, 0, 0}
                                                          (HMul.hMul.{0, 0, 0}
                                                            (HMul.hMul.{0, 0, 0} C
                                                              (HAdd.hAdd.{0, 0, 0}
                                                                (HAdd.hAdd.{0, 0, 0} HT
                                                                  (HMul.hMul.{0, 0, 0} (2 : Real) H2))
                                                                (3 : Real)))
                                                            invW)
                                                          (HMul.hMul.{0, 0, 0}
                                                            (HMul.hMul.{0, 0, 0} ε
                                                              (HAdd.hAdd.{0, 0, 0}
                                                                (HAdd.hAdd.{0, 0, 0} H1
                                                                  (HMul.hMul.{0, 0, 0} (2 : Real) H2))
                                                                (3 : Real)))
                                                            invW))
                                                        remRow) := by sorry
