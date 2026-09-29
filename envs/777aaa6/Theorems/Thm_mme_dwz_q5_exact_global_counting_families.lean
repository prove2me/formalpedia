-- Prove2me | Theorems.Thm_mme_dwz_q5_exact_global_counting_families
-- name    : mme_dwz_q5_exact_global_counting_families
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T21:57:12.859256+00:00
-- url     : https://prove2.me/theorems/a2028a1d-7f6a-4218-ac8b-577f493ec553
-- title:
--   Exact q=5 global families, ambient degrees, and useful Z-compatibility counts
-- statement:
--   Use the fixed public $q=5$ fourth-power candidate in its original 45-label order. For a label $c\in C=\{0,\ldots,44\}$, write $(I_c,J_c,L_c)$ for its coarse address, $a_c$ for its integer outer numerator, and $p_c$ for its unchanged parent Z profile. Write $d_c>0$ and $b_{c,\ell}$ for that profile's denominator and counts, where $0\le\ell\le4$. The public outer scale is $A=2\cdot10^{15}$.
--
--   For every positive integer $t$, define
--   $$
--   D=\prod_{c\in C}d_c,\qquad
--   m_c=\frac{a_cDt}{d_c},\qquad
--   n_c=d_cm_c,\qquad N=\sum_cn_c.
--   $$
--   The quotients are exact integers. Then
--   $$
--   D>0,\qquad n_c=a_cDt>0,\qquad N=ADt>0.
--   $$
--   Set $\mu_{Z,c}(\ell)=b_{c,\ell}m_c$. The boundary X and Y count rows are the reflected Z rows: $\mu_{X,c}(\ell)=\mu_{Z,c}(4-\ell)$ when $J_c=0$, and $\mu_{Y,c}(\ell)=\mu_{Z,c}(4-\ell)$ when $I_c=0$; the other X/Y rows are zero. Let $s_i(c)$ denote coordinate $i$ of the coarse address and set
--   $$
--   M_i(g)=\sum_{c:s_i(c)=g}n_c.
--   $$
--   All 27 bounded-grade marginals equal their stored public integer marginal numerator times $Dt$.
--
--   There is a finite indexed ambient family $w_a:\{0,\ldots,N-1\}\to C$, with a nonempty target set $T$, satisfying all of the following.
--
--   1. Its coarse addresses $A_a(i,x)=s_i(w_a(x))$ enumerate exactly once all supported address triples with marginal counts $M$. Both the label words and coarse addresses are injectively indexed. The ambient index set is the entire finite index universe.
--
--   2. The targets are exactly the words of joint type $n$, every such word is present, and
--   $$
--   |T|=\frac{N!}{\prod_c n_c!}.
--   $$
--   Every target has a component-preserving bijection of its positions with $\coprod_c\{0,\ldots,n_c-1\}$.
--
--   3. Write $\mathcal S=\{s\in\{0,\ldots,8\}^3:s_0+s_1+s_2=8\}$ and let $\mathcal H_N(M)$ consist of all integer tables $h:\mathcal S\to\{0,\ldots,N\}$ with the three prescribed marginals. Every ambient star in mode $i$ has exactly
--   $$
--   D_i=\sum_{h\in\mathcal H_N(M)}\prod_{g=0}^{8}
--   \frac{M_i(g)!}{\prod_{s:s_i=g}h(s)!}
--   $$
--   indices, independently of its center.
--
--   4. For each target $a$, a useful fine word actually exists. Such a word assigns four atomic grades in $\{0,1,2\}$ to each position $x$, with total $L_{w_a(x)}$ and with exactly $\mu_{Z,c}(\ell)$ occurrences of each label $c$ and left-half grade $\ell$.
--
--   For every useful fine word at a target, the number of compatible target indices is the following profile-only integer $W$, and the number other than the original target is exactly $W-1$. To define it, put
--   $$
--   B=\{c:I_c=0\text{ or }J_c=0\},\qquad
--   F_{g,\ell}=\sum_{c:L_c=g}\mu_{Z,c}(\ell).
--   $$
--   Let $\Delta=C\sqcup\{0,\ldots,8\}$ be a disjoint union, and define $\eta(c)$ to be the label $c$ in its first summand when $c\in B$, and the grade $L_c$ in its second summand otherwise. For $\delta\in\Delta$, define the pooled counts
--   $$
--   q_{\delta,g,\ell}=
--   \begin{cases}
--   \mu_{Z,c}(\ell),&\delta=c\text{ in the first summand},\ c\in B,\ L_c=g,\\
--   F_{g,\ell}-\displaystyle\sum_{c\in B:L_c=g}\mu_{Z,c}(\ell),
--    &\delta=g\text{ in the second summand},\\
--   0,&\text{otherwise}.
--   \end{cases}
--   $$
--   Then the exact count is
--   $$
--   W=
--   \left(\prod_{g=0}^{8}\prod_{\ell=0}^{4}
--   \frac{F_{g,\ell}!}{\prod_{\delta\in\Delta}q_{\delta,g,\ell}!}\right)
--   \left(\prod_{\delta\in\Delta}
--   \frac{\left(\sum_{g,\ell}q_{\delta,g,\ell}\right)!}
--   {\prod_{c:\eta(c)=\delta}n_c!}\right).
--   $$
--   Compatibility means preservation of the positionwise total Z grade and the prescribed split counts on boundary labels. Every compatible competitor also satisfies the paper's aggregate split condition: its number of positions of coarse Z grade $g$ and left-half grade $\ell$ is $F_{g,\ell}$.
--
--   These are exact finite conclusions for the original rational-replay candidate data. No target existence, position bijection, ambient degree bound, compatibility count, or useful-word existence is assumed. The theorem does not provide an asymptotic entropy estimate, a positive-component value bound, or a matrix-multiplication exponent conclusion.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5 , Section 3.7 Definition 3.5 (joint and marginal types), Section 3.10 (full marginal ambient and good triples), and Section 6.1 Definition 6.1 with Section 6.2 (usefulness, boundary/aggregate Z compatibility and counts). Concrete denominator-cleared finite instantiation for the released q=5 fourth-power candidate power4_dup_2.371919.mat at https://osf.io/dta6p/files/zx3yf . Uses the existing public rational outer distribution and unchanged rational-replay parent profiles, not literal binary64 equality. The bundled finite interface is derived from these sources, not attributed as a verbatim numbered theorem.

import Definitions.Def_mme_dwz_q5_exact_global_profile_data
import Definitions.Def_mme_dwz_simultaneous_CW_projection_data
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma

open BigOperators MME.DWZSimultaneous MME.CompleteSplit
  MME.DWZQ5ExactData MME.DWZFourthGlobalWitness
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 100000

theorem mme_dwz_q5_exact_global_counting_families (t : ℕ) (ht : 0 < t) :
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
    0 < D ∧
    N = scale * (D * t) ∧
    (∀ c : Fin 45, n c = component c * (D * t)) ∧
    (∀ c : Fin 45, 0 < n c) ∧
    (∀ (i : Fin 3) (g : Fin 9), M i g.val = marginal i g * (D * t)) ∧
    0 < N ∧
    (∃ (R : ℕ) (word : Fin R → Fin N → Fin 45) (targets : Finset (Fin R)),
      Function.Injective word ∧
      Function.Injective (owner word shape) ∧
      (∀ a, SameMarginal M (owner word shape a)) ∧
      (∀ a, Supported 8 (owner word shape a)) ∧
      (∀ a : CoarseAddress N, Supported 8 a → SameMarginal M a →
        ∃ b, owner word shape b = a) ∧
      (∀ a, a ∈ targets ↔
        ∀ c, Fintype.card {x : Fin N // word a x = c} = n c) ∧
      (∀ w : Fin N → Fin 45, (∀ c, Fintype.card {x : Fin N // w x = c} = n c) →
        ∃ a ∈ targets, word a = w) ∧
      targets.card = N.factorial / ∏ c, (n c).factorial ∧
      targets.Nonempty ∧
      (∃ positions : ∀ a : Fin R, a ∈ targets → (Fin N ≃ Σ c, Fin (n c)),
        ∀ a ha c r, word a ((positions a ha).symm ⟨c, r⟩) = c) ∧
      (∀ (mode : Fin 3) (a : Fin R),
        (Finset.univ.filter (fun b ↦ owner word shape b mode =
          owner word shape a mode)).card = degree mode) ∧
      (∀ a ∈ targets, ∀ f : FineWord 3 N,
        Graded word shape a 2 f → Profile word fourthLeftTag mu a 2 f →
        (targets.filter (fun b ↦ ZCompatible word shape fourthLeftTag mu b f)).card = W ∧
        (targets.filter (fun b ↦ b ≠ a ∧ ZCompatible word shape fourthLeftTag mu b f)).card = W - 1 ∧
        (∀ b, ZCompatible word shape fourthLeftTag mu b f →
          ∀ (g : Fin 9) (l : Fin 5),
            Fintype.card {x : Fin N // shape (word b x) 2 = g.val ∧
              fourthLeftTag (f x) = l} = F (g,l))) ∧
      (∀ a ∈ targets, ∃ f : FineWord 3 N,
        Graded word shape a 2 f ∧ Profile word fourthLeftTag mu a 2 f)) := by sorry
