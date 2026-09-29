-- Prove2me | Theorems.Thm_mme_dwz_fourth_actual_indexed_fine_Z_compatibility_count
-- name    : mme_dwz_fourth_actual_indexed_fine_Z_compatibility_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T21:46:34.847267+00:00
-- url     : https://prove2.me/theorems/5b5b9de7-7c47-4ecf-a1d3-cd64c5ad5c4c
-- title:
--   Actual fourth-level fine-Z compatibility: useful words and exact competitor counts
-- statement:
--   Fix component labels $c\in C=\{0,\ldots,k-1\}$ with shapes $(x_c,y_c,z_c)$ and $z_c\in\{0,\ldots,8\}$. Let $n_c$ and $\mu_{c,l}$ be nonnegative integer counts, with
--   $$
--   \sum_{l=0}^{4}\mu_{c,l}=n_c,\qquad
--   \mu_{c,l}>0\Longrightarrow l\le z_c\le l+4.
--   $$
--   Suppose the indexed target family contains exactly one copy of every word $g:\{0,\ldots,N-1\}\to C$ with histogram $n$. Write $B=\{c:x_c=0\text{ or }y_c=0\}$ and
--   $$
--   F_{g,l}=\sum_{c:z_c=g}\mu_{c,l}.
--   $$
--   A fine word consists of one vector in $\{0,1,2\}^4$ at each position. Its total grade is the sum of all four entries, and its left tag is the sum of the first two. A fine word is useful for a target when its total grades agree with that target and every component/tag joint count equals $\mu_{c,l}$.
--
--   For $D=C\sqcup\{0,\ldots,8\}$, let $\chi(c)=\operatorname{inl}(c)$ on $B$ and $\chi(c)=\operatorname{inr}(z_c)$ otherwise. Define
--   $$
--   m_{\operatorname{inl}(c),(g,l)}=
--   \begin{cases}\mu_{c,l}&c\in B,\ z_c=g,\\0&\text{otherwise},\end{cases}
--   $$
--   $$
--   m_{\operatorname{inr}(g'),(g,l)}=
--   \begin{cases}F_{g,l}-\displaystyle\sum_{\substack{c\in B\\z_c=g}}\mu_{c,l}&g'=g,\\0&g'\ne g.\end{cases}
--   $$
--   Set the profile-only integer
--   $$
--   W=
--   \left(\prod_{i\in\{0,\ldots,8\}\times\{0,\ldots,4\}}
--   \frac{F_i!}{\prod_{d\in D}m_{d,i}!}\right)
--   \left(\prod_{d\in D}
--   \frac{(\sum_i m_{d,i})!}{\prod_{c:\chi(c)=d}n_c!}\right).
--   $$
--
--   Then:
--
--   1. Every target has an actual useful fine word.
--   2. Every useful fine word has joint total-grade/left-tag histogram $F$, independent of the chosen useful word.
--   3. For any candidate owner, grading and the boundary joint-count conditions are equivalent to those same conditions together with the aggregate grade/tag counts $F$. Thus the aggregate compatibility condition is recovered from the useful witness.
--   4. For every useful owner $j$ and useful fine word $f$,
--   $$
--   |\{b\in\mathrm{targets}: b\text{ is Z-compatible with }f\}|=W,
--   \qquad
--   |\{b\in\mathrm{targets}:b\ne j,\ b\text{ is Z-compatible with }f\}|=W-1.
--   $$
--
--   This is an exact finite fourth-level compatibility count and uniform competitor bound, including zero counts and $N=0$. The formula depends only on the component counts, shapes, and prescribed Z profiles. It is not an asymptotic entropy estimate or a matrix-multiplication exponent claim.
--
--   **Formalization Note.** The public predicate `ZCompatible` stores grading and boundary conditions. The theorem explicitly restores the paper's aggregate condition rather than silently identifying the predicates. The input `coarse` is the bounded representation of the Z shape, and only `mu 2` is used.
-- source:
--   Derived exact finite version of Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.1 Definitions 6.1 and 6.3; Section 6.2 Lemma 6.7 and Claim 6.8. https://arxiv.org/html/2210.10173v5#S6.SS1 . Uses accepted useful-witness assignment counting, constructs actual CompleteWord 3 witnesses, derives aggregate compatibility, and transfers through an exact indexed target-word equivalence.

import Definitions.Def_mme_dwz_simultaneous_CW_projection_data

open BigOperators MME.CompleteSplit MME.DWZSimultaneous
open scoped Classical
set_option autoImplicit false

theorem mme_dwz_fourth_actual_indexed_fine_Z_compatibility_count {N k R : ℕ}
    (component : Fin R → Fin N → Fin k)
    (shape : Fin k → Fin 3 → ℕ) (coarse : Fin k → Fin 9)
    (hshape : ∀ c, (coarse c).val = shape c 2)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ)
    (targets : Finset (Fin R))
    (hn : ∀ b ∈ targets, ∀ c, Fintype.card {t : Fin N // component b t = c} = n c)
    (hinj : Set.InjOn component (targets : Set (Fin R)))
    (hcomplete : ∀ g : Fin N → Fin k,
      (∀ c, Fintype.card {t : Fin N // g t = c} = n c) →
      ∃ b ∈ targets, component b = g)
    (hrows : ∀ c, (∑ l, mu 2 c l) = n c)
    (hsupport : ∀ c l, 0 < mu 2 c l →
      l.val ≤ (coarse c).val ∧ (coarse c).val ≤ l.val + 4) :
    let Boundary := fun c ↦ shape c 0 = 0 ∨ shape c 1 = 0
    let F : Fin 9 × Fin 5 → ℕ := fun i ↦
      ∑ c : {c : Fin k // coarse c = i.1}, mu 2 c.val i.2
    let collapse : Fin k → Fin k ⊕ Fin 9 := fun c ↦
      if Boundary c then Sum.inl c else Sum.inr (coarse c)
    let mass : (Fin k ⊕ Fin 9) × (Fin 9 × Fin 5) → ℕ
      | (Sum.inl c, (g,l)) => if Boundary c ∧ coarse c = g then mu 2 c l else 0
      | (Sum.inr g', (g,l)) => if g' = g then F (g,l) -
          ∑ c ∈ Finset.univ.filter (fun c ↦ Boundary c ∧ coarse c = g), mu 2 c l
        else 0
    let W : ℕ :=
      (∏ i : Fin 9 × Fin 5, (F i).factorial /
        ∏ di : {di : (Fin k ⊕ Fin 9) × (Fin 9 × Fin 5) // di.2 = i},
          (mass di.val).factorial) *
      (∏ d : Fin k ⊕ Fin 9, (∑ i, mass (d,i)).factorial /
        ∏ c : {c : Fin k // collapse c = d}, (n c.val).factorial)
    (∀ j ∈ targets, ∃ f : FineWord 3 N,
      Graded component shape j 2 f ∧ Profile component fourthLeftTag mu j 2 f) ∧
    ∀ j ∈ targets, ∀ f : FineWord 3 N,
      Graded component shape j 2 f ∧ Profile component fourthLeftTag mu j 2 f →
      (∀ g : Fin 9, ∀ l : Fin 5,
        Fintype.card {t : Fin N // (∑ r, (f t r).val) = g.val ∧ fourthLeftTag (f t) = l} = F (g,l)) ∧
      (∀ b : Fin R, ZCompatible component shape fourthLeftTag mu b f ↔
        Graded component shape b 2 f ∧
        (∀ g : Fin 9, ∀ l : Fin 5,
          Fintype.card {t : Fin N // shape (component b t) 2 = g.val ∧ fourthLeftTag (f t) = l} = F (g,l)) ∧
        ∀ c, Boundary c → ∀ l,
          Fintype.card {t : Fin N // component b t = c ∧ fourthLeftTag (f t) = l} = mu 2 c l) ∧
      (targets.filter (fun b ↦ ZCompatible component shape fourthLeftTag mu b f)).card = W ∧
      (targets.filter (fun b ↦ b ≠ j ∧ ZCompatible component shape fourthLeftTag mu b f)).card = W - 1 := by sorry
