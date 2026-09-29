-- Prove2me | Theorems.Thm_mme_dwz_attainable_profile_grouping_mask_card
-- name    : mme_dwz_attainable_profile_grouping_mask_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T08:08:19.142162+00:00
-- url     : https://prove2.me/theorems/5118b98e-be27-4bcc-90be-554d1bf4a49a
-- title:
--   Grouping attainable profile blocks preserves every mask count
-- statement:
--   Let $P,C,A$ be finite sets of positions, components, and block labels, respectively, and let $W$ be any set of profile tags. Write $[n]=\{0,\ldots,n-1\}$, including $[0]=\varnothing$. Fix a component map $\kappa:P\to C$, integers $n_c\ge0$, and a grouping bijection
--   $$
--   e:P\simeq\bigsqcup_{c\in C}[n_c],
--   \qquad \kappa(e^{-1}(c,r))=c.
--   $$
--
--   For each component $c$, let $I_c$ be an arbitrary index set, let $G_c\subseteq I_c$ be its allowed indices, and let $\lambda_c:I_c\to A$ assign block labels. Define the attainable labels by the actual image
--   $$
--   F_c=\{\lambda_c(a):a\in G_c\}.
--   $$
--   The label maps need not be injective or surjective. Also fix tag maps $\theta_c:A\to W$ and exact nonnegative integer counts $\mu_c(w)$.
--
--   Let $\mathcal U$ consist of the words $f:P\to A$ satisfying $f(p)\in F_{\kappa(p)}$ for every position and
--   $$
--   |\{p\in P:\kappa(p)=c,\ \theta_c(f(p))=w\}|=\mu_c(w)
--   \qquad(c\in C,\ w\in W).
--   $$
--   For each $c$, let $\mathcal U_c$ consist of the words $g:[n_c]\to F_c$, viewed as $A$-valued words, satisfying
--   $$
--   |\{r\in[n_c]:\theta_c(g(r))=w\}|=\mu_c(w)
--   \qquad(w\in W).
--   $$
--
--   There is a bijection
--   $$
--   E:\mathcal U\simeq\prod_{c\in C}\mathcal U_c,
--   \qquad (Ef)_c(r)=f(e^{-1}(c,r)).
--   $$
--   Every $f\in\mathcal U$ has an allowed-index representative: there are $a_p\in G_{\kappa(p)}$ with $\lambda_{\kappa(p)}(a_p)=f(p)$ for every $p$. Furthermore, every mask $M$ on $\mathcal U$ has exactly the same cardinality after transport:
--   $$
--   |\{f\in\mathcal U:M(f)\}|
--   =
--   \left|\left\{g\in\prod_{c\in C}\mathcal U_c:
--   M(E^{-1}g)\right\}\right|.
--   $$
--
--   This provides the finite profile/block-index transport needed when regrouping component positions. In a basis application, the sets $I_c$ and $G_c$ must be instantiated with the genuine basis indices and coarse-grade conditions. Distinct labels, not their possibly many index representatives, are counted. Zero component counts and empty allowed fibers are permitted; the theorem does not assume or assert that the requested profiles are realizable. No tensor map, nonzero tensor-support claim, complete standard-product identification, or hole-repair conclusion is asserted.
-- source:
--   Derived finite grouping and mask-cardinality lemma for Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5#S5.SS1 , Section 5.1, Definitions 5.3–5.4 (component-indexed small blocks and exact-profile available Z-blocks), with masks corresponding to Definition 5.5. This is a generic image-based combinatorial formalization of the block-index regrouping step, including zero multiplicities and empty fibers; it is not a separately numbered theorem or the tensor-normalization assertion in the paper.

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic

open scoped Classical

set_option autoImplicit false

theorem mme_dwz_attainable_profile_grouping_mask_card
    {P C A W : Type*} [Fintype P] [Fintype C] [Fintype A]
    {I : C → Type*}
    (cell : P → C) (n : C → ℕ)
    (positions : P ≃ Σ c, Fin (n c))
    (hcell : ∀ c r, cell (positions.symm ⟨c, r⟩) = c)
    (good : (c : C) → I c → Prop) (label : (c : C) → I c → A)
    (tag : C → A → W) (mu : C → W → ℕ) :
    let Global := {f : P → A //
      (∀ p, ∃ a : I (cell p), good (cell p) a ∧ label (cell p) a = f p) ∧
      ∀ c w, Fintype.card {p : P // cell p = c ∧ tag c (f p) = w} = mu c w}
    let Grouped := (c : C) → {g : Fin (n c) → A //
      (∀ r, ∃ a : I c, good c a ∧ label c a = g r) ∧
      ∀ w, Fintype.card {r : Fin (n c) // tag c (g r) = w} = mu c w}
    ∃ E : Global ≃ Grouped,
      (∀ f c r, (E f c).val r = f.val (positions.symm ⟨c, r⟩)) ∧
      (∀ f : Global, ∃ a : (p : P) → I (cell p),
        (∀ p, good (cell p) (a p)) ∧ ∀ p, label (cell p) (a p) = f.val p) ∧
      ∀ mask : Global → Prop,
        Fintype.card {f : Global // mask f} =
          Fintype.card {g : Grouped // mask (E.symm g)} := by sorry
