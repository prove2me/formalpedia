-- Prove2me | Theorems.Thm_mme_dwz_q5_actual_standard_products_of_numeric_budgets
-- name    : mme_dwz_q5_actual_standard_products_of_numeric_budgets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T21:44:42.270832+00:00
-- url     : https://prove2.me/theorems/08f4548a-c75c-4bb6-9394-bee622308d5b
-- title:
--   Actual q=5 standard-product extraction under explicit numerical budgets
-- statement:
--   Fix the public $q=5$ candidate, with coarse labels $c\in C=\{0,\ldots,44\}$, addresses $(I_c,J_c,L_c)$, positive outer numerators $a_c$, and unchanged parent Z profiles $p_c$ with denominators $d_c$ and counts $b_{c,\ell}$. For every integer $t>0$, set
--   $
--   D=\prod_c d_c,\quad m_c=\frac{a_cDt}{d_c},\quad n_c=d_cm_c,\quad
--   N=\sum_c n_c,\quad T=\frac{N!}{\prod_c n_c!}.
--   $
--   The denominator divisions are exact. Put $\mu_c(\ell)=b_{c,\ell}m_c$, $s(c)=(I_c,J_c,L_c)$, and $M_i(g)=\sum_{c:s_i(c)=g}n_c$.
--
--   Let $\mathcal H$ be all integer tables $h$ on $\{s\in\{0,\ldots,8\}^3:s_0+s_1+s_2=8\}$, with entries between $0$ and $N$ and all three marginals equal to $M$. Define the full ambient mode-star counts
--   $
--   D_i=\sum_{h\in\mathcal H}\prod_{g=0}^{8}
--   \frac{M_i(g)!}{\prod_{s:s_i=g}h(s)!}.
--   $
--   For the Z count, put $B=\{c:I_c=0\text{ or }J_c=0\}$, $F_{g,\ell}=\sum_{c:L_c=g}\mu_c(\ell)$, and $\Delta=C\sqcup\{0,\ldots,8\}$. The collapsed label $\eta(c)$ is $c$ in the first summand for $c\in B$, and $L_c$ in the second otherwise. Set
--   $
--   q_{c,g,\ell}=
--   \begin{cases}\mu_c(\ell)&c\in B,\ L_c=g,\\0&\text{otherwise}\end{cases}
--   $
--   for first-summand labels, and set $q_{g,g,\ell}=F_{g,\ell}-\sum_{c\in B:L_c=g}\mu_c(\ell)$ for second-summand labels, with their other entries zero. Define
--   $
--   W=
--   \left(\prod_{g,\ell}\frac{F_{g,\ell}!}{\prod_{\delta\in\Delta}q_{\delta,g,\ell}!}\right)
--   \left(\prod_{\delta\in\Delta}
--   \frac{(\sum_{g,\ell}q_{\delta,g,\ell})!}{\prod_{c:\eta(c)=\delta}n_c!}\right).
--   $
--   This is the exact compatible-target count; the competing-target count is $W-1$.
--
--   Let $p>8$ be an odd prime and let $S\subseteq\{0,\ldots,\lfloor p/2\rfloor-1\}$ be three-term-progression-free. For every $r\in\mathbb N$, the numerical conditions
--   $
--   4\max\{D_0,D_1\}\le p,\qquad 8(W-1)\le p,\qquad
--   8p^2r(3N+2)\le 3T|S|
--   $
--   imply, over every field, the actual tensor restriction
--   $
--   \bigoplus_{j=1}^{r}\ \bigotimes_{c\in C}
--   P_{p_c,m_c}(T_{I_c,J_c,L_c})
--   \ \preceq\ CW_5^{\otimes 4N}.
--   $
--   Here $P_{p_c,m_c}$ is the prescribed-Z power with the canonical fourth-constituent basis and left-square grade. No family, position-bijection, collision-count, or tensor-realization hypothesis remains. The original rational-replay profiles are not retuned. The case $r=0$ is allowed. The theorem leaves the displayed numerical budgets conditional: it does not establish an entropy estimate, a suitable prime and progression-free set, the scalar value surplus, or a matrix-multiplication exponent bound.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5 , Sections 3.7 and 3.10 (joint/marginal type families and asymmetric hashing), Section 5.2 (repair), and Sections 6.1–6.2 (useful Z blocks and compatibility). Concrete finite specialization for the released q=5 fourth-power candidate power4_dup_2.371919.mat at https://osf.io/dta6p/files/zx3yf . Uses unchanged public rational-replay parent profiles. This finite numeric-budget corollary is derived from these sources, not a verbatim numbered theorem.

import Definitions.Def_mme_dwz_q5_exact_global_profile_data
import Definitions.Def_mme_complete_split_cw_fourth_labels
import Definitions.Def_mme_CW_2376_address_block
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.Pi

open BigOperators MME MME.TensorObj MME.StothersFourth
  MME.DWZRestrictedValue MME.CompleteSplit.CWFourth
  MME.DWZQ5ExactData MME.DWZFourthGlobalWitness
open scoped Classical
universe u
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem mme_dwz_q5_actual_standard_products_of_numeric_budgets
    {K : Type u} [Field K] (t modulus r : ℕ) (ht : 0 < t)
    [Fact modulus.Prime]
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (modulus / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) (hpodd : Odd modulus)
    (hmodulus : 8 < modulus) :
    let D := ∏ c : Fin 45, (rawProfile c).denominator
    let m := fun c : Fin 45 ↦ component c * (D * t) / (rawProfile c).denominator
    let n := fun c : Fin 45 ↦ (rawProfile c).length (m c)
    let N := ∑ c : Fin 45, n c
    let shape : Fin 45 → Fin 3 → ℕ := fun c i ↦ (coarseAddress c i).val
    let z := fun c (l : Fin 5) ↦ (rawProfile c).count l * m c
    let mu : Fin 3 → Fin 45 → Fin 5 → ℕ := fun
      | 0, c, l => if shape c 1 = 0 then z c (Fin.rev l) else 0
      | 1, c, l => if shape c 0 = 0 then z c (Fin.rev l) else 0
      | 2, c, l => z c l
    let M : Fin 3 → ℕ → ℕ :=
      fun i g ↦ ∑ c : {c : Fin 45 // shape c i = g}, n c.val
    let Cell := {s : Fin 3 → Fin 9 // (∑ i, (s i).val) = 8}
    let tables : Finset (Cell → Fin (N + 1)) := Finset.univ.filter (fun h ↦
      ∀ i : Fin 3, ∀ g : Fin 9,
        (∑ s : {s : Cell // s.val i = g}, (h s.val).val) = M i g.val)
    let degree := fun mode : Fin 3 ↦
      ∑ h ∈ tables, ∏ g : Fin 9, (M mode g.val).factorial /
        ∏ s : {s : Cell // s.val mode = g}, ((h s.val).val).factorial
    let coarse := fun c : Fin 45 ↦ coarseAddress c 2
    let boundary := fun c : Fin 45 ↦ shape c 0 = 0 ∨ shape c 1 = 0
    let F := fun i : Fin 9 × Fin 5 ↦
      ∑ c : {c : Fin 45 // coarse c = i.1}, mu 2 c.val i.2
    let pooled : (Fin 45 ⊕ Fin 9) × (Fin 9 × Fin 5) → ℕ := fun
      | (Sum.inl c, (g,l)) => if boundary c ∧ coarse c = g then mu 2 c l else 0
      | (Sum.inr g', (g,l)) => if g' = g then F (g,l) -
          ∑ c ∈ Finset.univ.filter (fun c ↦ boundary c ∧ coarse c = g), mu 2 c l
        else 0
    let collapse := fun c : Fin 45 ↦ if boundary c then Sum.inl c else Sum.inr (coarse c)
    let W :=
      (∏ i : Fin 9 × Fin 5, (F i).factorial /
        ∏ di : {di : (Fin 45 ⊕ Fin 9) × (Fin 9 × Fin 5) // di.2 = i},
          (pooled di.val).factorial) *
      (∏ d : Fin 45 ⊕ Fin 9, (∑ i, pooled (d,i)).factorial /
        ∏ c : {c : Fin 45 // collapse c = d}, (n c.val).factorial)
    4 * max (degree 0) (degree 1) ≤ modulus →
    8 * (W - 1) ≤ modulus →
    8 * modulus ^ 2 * (r * (3 * N + 2)) ≤
      3 * (N.factorial / ∏ c, (n c).factorial) * S.card →
    TensorObj.Restrict
      (bigAdd (fun _ : Fin r ↦ kronFin 45 (fun c ↦ prescribedZPower
        (cwFourthConstituent K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2))
        (constituentBasis K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2) 2)
        (fun a : LiftedCoarseCoordinate.{u} 5 (coarseAddress c 2) ↦
          cwSquarePairGrade 5 a.down.val.1)
        (rawProfile c) (m c))))
      ((CWObj K 5).kronPow (N * 4)) := by sorry
