-- Prove2me | Theorems.Thm_mme_dwz_boundary_compatible_assignment_card_of_useful_witness
-- name    : mme_dwz_boundary_compatible_assignment_card_of_useful_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T20:37:29.046182+00:00
-- url     : https://prove2.me/theorems/8c6068e9-f18b-4156-a5a7-8c9e814ab4ad
-- title:
--   Exact boundary-compatible assignment count from an actual witness
-- statement:
--   Let $A,C,K,L$ be finite sets, $f:A\to K\times L$ a fine-label map, $q:C\to K$ a coarse-label map, and $B\subseteq C$ the boundary labels. Suppose an actual assignment $g_0:A\to C$ satisfies $q(g_0(a))=f(a)_1$. Define
--   $$
--   n_c=|\{a:g_0(a)=c\}|,\quad b_{c,l}=|\{a:g_0(a)=c,\ f(a)_2=l\}|,\quad F_{k,l}=|\{a:f(a)=(k,l)\}|.
--   $$
--   Collapse boundary labels individually and pool all other labels by their coarse label:
--   $$
--   \chi(c)=\begin{cases}\operatorname{inl}(c)&c\in B,\\ \operatorname{inr}(q(c))&c\notin B.\end{cases}
--   $$
--   For $d\in C\sqcup K$ and $i=(k,l)\in K\times L$, define $m_{d,i}$ by
--   $$
--   m_{\operatorname{inl}(c),(k,l)}
--   =\begin{cases}b_{c,l}&c\in B,\ q(c)=k,\\0&\text{otherwise},\end{cases}
--   $$
--   $$
--   m_{\operatorname{inr}(k'),(k,l)}
--   =\begin{cases}F_{k,l}-\displaystyle\sum_{\substack{c\in B\\q(c)=k}}b_{c,l}&k'=k,\\0&k'\ne k.\end{cases}
--   $$
--   Let $\mathcal G$ consist of assignments $g:A\to C$ having histogram $n$, satisfying $q(g(a))=f(a)_1$, and having boundary joint counts $|\{a:g(a)=c,\ f(a)_2=l\}|=b_{c,l}$ for every $c\in B$. Then
--   $$
--   |\mathcal G|=
--   \left(\prod_{i\in K\times L}\frac{F_i!}{\prod_{d\in C\sqcup K}m_{d,i}!}\right)
--   \left(\prod_{d\in C\sqcup K}\frac{(\sum_i m_{d,i})!}{\prod_{c:\chi(c)=d}n_c!}\right).
--   $$
--   This finite witness specialization supplies the boundary-versus-pooled compatibility count without separate row or column balance assumptions. It allows empty sets and zero counts. It is a counting input to the DWZ compatibility analysis, not an asymptotic probability or tensor-value theorem.
-- source:
--   Derived finite witness specialization of Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.2, Definition 6.6 and Lemma 6.7 (boundary/pooled compatibility counts), https://arxiv.org/html/2210.10173v5#S6.SS2 . Uses the accepted finite counting theorem mme_dwz_boundary_compatible_assignment_card; witness histograms discharge its balance hypotheses.

import Theorems.Thm_mme_dwz_boundary_compatible_assignment_card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Basic

open scoped BigOperators
set_option autoImplicit false

theorem mme_dwz_boundary_compatible_assignment_card_of_useful_witness {A C K L : Type*}
    [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
    [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    (fine : A → K × L) (coarse : C → K)
    (Boundary : C → Prop) [DecidablePred Boundary]
    (g0 : A → C) (hcoarse : ∀ a, coarse (g0 a) = (fine a).1) :
    let n : C → ℕ := fun c ↦ Fintype.card {a : A // g0 a = c}
    let b : C → L → ℕ := fun c l ↦
      Fintype.card {a : A // g0 a = c ∧ (fine a).2 = l}
    let collapse : C → C ⊕ K :=
      fun c ↦ if Boundary c then Sum.inl c else Sum.inr (coarse c)
    let m : (C ⊕ K) × (K × L) → ℕ
      | (Sum.inl c, (k, l)) => if Boundary c ∧ coarse c = k then b c l else 0
      | (Sum.inr k', (k, l)) =>
          if k' = k then Fintype.card {a : A // fine a = (k, l)} -
            ∑ c ∈ Finset.univ.filter (fun c : C ↦ Boundary c ∧ coarse c = k), b c l
          else 0
    Nat.card {g : A → C //
      (∀ c, Fintype.card {a : A // g a = c} = n c) ∧
      (∀ a, coarse (g a) = (fine a).1) ∧
      ∀ c, Boundary c → ∀ l,
        Fintype.card {a : A // g a = c ∧ (fine a).2 = l} = b c l} =
      (∏ i, (Fintype.card {a : A // fine a = i}).factorial /
        ∏ di : {di : (C ⊕ K) × (K × L) // di.2 = i}, (m di.val).factorial) *
      (∏ d, (∑ i, m (d, i)).factorial /
        ∏ c : {c : C // collapse c = d}, (n c.val).factorial) := by sorry
