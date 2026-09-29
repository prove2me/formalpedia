-- Prove2me | Theorems.Thm_mme_dwz_q5_exact_global_profile_certificate
-- name    : mme_dwz_q5_exact_global_profile_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T21:19:31.990159+00:00
-- url     : https://prove2.me/theorems/e9bdb883-310a-4029-92cd-4e72544bbe8e
-- title:
--   Kernel certificate for the exact q=5 outer type and unchanged parent Z profiles
-- statement:
--   Consider the fixed $q=5$ fourth-level candidate data, in the public 45-cell order. Write $\sigma(c)=(I_c,J_c,L_c)$ for its public coarse address, $\alpha_c$ for its public rational outer weight, $a_c$ for its stored integer numerator, and $A=2\cdot10^{15}$ for the common scale. Then
--   $$
--   a_c>0,\qquad \sum_{c=0}^{44}a_c=A,\qquad \frac{a_c}{A}=\alpha_c
--   \quad(c=0,\ldots,44).
--   $$
--   The address table enumerates the entire supported fourth-level set exactly once:
--   $$
--   \{0,\ldots,44\}\ \simeq
--   \{(I,J,L)\in\{0,\ldots,8\}^3:I+J+L=8\},
--   $$
--   with the bijection's value at $c$ equal to the literal public address $\sigma(c)$.
--
--   The stored integer marginal tables $M_X,M_Y,M_Z$ satisfy all 27 exact identities and all three normalizations:
--   $$
--   M_i(g)=\sum_{c:\sigma(c)_i=g}a_c,\qquad
--   \sum_{g=0}^{8}M_i(g)=A,\qquad M_X=M_Y.
--   $$
--   Finally, let $p_c$ be the unchanged exact rational-replay parent Z profile, with integer counts $b_{c,\ell}$ and positive denominator $d_c$. Every positive count lies on a realizable left-square split:
--   $$
--   b_{c,\ell}>0\quad\Longrightarrow\quad
--   \ell\leq L_c\leq\ell+4.
--   $$
--   The profile objects already include the constructor identities $\sum_{\ell=0}^4 b_{c,\ell}=d_c$ and $d_c>0$.
--
--   All assertions are exact finite arithmetic or finite bijections. The parent profiles are not averaged or retuned. This certifies the literal data needed to build target and ambient families; it does not assert any entropy ceiling, tensor extraction, or final value surplus.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions3.5 and3.7 and Sections6.1–6.2; released power4_dup_2.371919.mat at https://osf.io/dta6p/files/zx3yf . Exact arithmetic certificate for existing public rational-global data f99d9be9-2a29-4f1d-a088-6deb77a2e185 and the unchanged exact rational-replay parent-profile data (top-level ledger objects139–183). The ledger's scalar-induction facade is not imported or assumed.

import Definitions.Def_mme_dwz_q5_exact_global_profile_data
import Mathlib.Data.Fintype.EquivFin

open BigOperators MME.DWZQ5ExactData MME.DWZFourthGlobalWitness
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem mme_dwz_q5_exact_global_profile_certificate :
    0 < scale ∧
    (∀ c : Fin 45, 0 < component c) ∧
    (∑ c : Fin 45, component c) = scale ∧
    (∀ c : Fin 45, (component c : ℚ) / scale = alpha c) ∧
    (∀ c : Fin 45, ∑ i : Fin 3, (coarseAddress c i).val = 8) ∧
    Function.Injective coarseAddress ∧
    (∀ (i : Fin 3) (g : Fin 9),
      (∑ c : Fin 45, if coarseAddress c i = g then component c else 0) =
        marginal i g) ∧
    (∀ i : Fin 3, ∑ g : Fin 9, marginal i g = scale) ∧
    (∀ g : Fin 9, marginal 0 g = marginal 1 g) ∧
    (∃ e : Fin 45 ≃ {v : Fin 3 → Fin 9 // (∑ i, (v i).val) = 8},
      ∀ c : Fin 45, (e c).val = coarseAddress c) ∧
    (∀ (c : Fin 45) (a : Fin 5), 0 < (rawProfile c).count a →
      a.val ≤ (coarseAddress c 2).val ∧ (coarseAddress c 2).val ≤ a.val + 4) := by sorry
