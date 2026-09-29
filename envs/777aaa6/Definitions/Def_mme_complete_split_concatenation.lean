-- Prove2me | Definitions.Def_mme_complete_split_concatenation
-- name    : mme_complete_split_concatenation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-06T21:18:14.701002+00:00
-- url     : https://prove2.me/theorems/383edb3e-8f9b-42ed-af37-8bdd5535ee90
-- title:
--   Literal complete-word concatenation and finite probability mixtures
-- statement:
--   A fine word of length $n$ is an ordered function from $\{0,\ldots,n-1\}$ to $\{0,1,2\}$. Splitting a word after its first $m$ entries is a bijection with a pair of words of lengths $m$ and $n$; its inverse is literal ordered concatenation.
--
--   For every level $\ell\ge1$, a complete word at level $\ell+1$ has twice the length $2^{\ell-1}$ of a level-$\ell$ word. The same bijection therefore identifies a parent complete word with its two child complete words. For real-valued word functions $p,q$ and a finite family $p_r$, define
--   $$
--   (p\mathbin{\times}q)(x\circ y)=p(x)q(y),\qquad
--   \operatorname{mix}_a(p_r)(w)=\sum_r a_r p_r(w).
--   $$
--   These definitions preserve literal order and full words. Nonnegativity, normalization, and exact marginal identities are separate theorems. No tensor extraction, empirical nonemptiness, or asymptotic value is assumed.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, printed p.14 (joint distributions on concatenated integer sequences and Definition3.4), and Proposition6.3, printed p.31 (regional full-profile mixtures of concatenation products). https://arxiv.org/abs/2404.16349v2. This is the elementary literal finite-profile layer, not the recursive tensor-extraction theorem.

import Definitions.Def_mme_complete_split_profile_projection
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators

open BigOperators

set_option autoImplicit false
set_option warningAsError true

universe u

namespace MME.CompleteSplit

/-- A literal word of n level-one grades, in their specified order. -/
abbrev FineWord (n : ℕ) := Fin n → Fin 3

/-- Split at position m; the inverse appends the two ordered words. -/
def fineWordSplitEquiv (m n : ℕ) : FineWord (m + n) ≃ FineWord m × FineWord n where
  toFun w := (fun i ↦ w (Fin.castAdd n i), fun i ↦ w (Fin.natAdd m i))
  invFun w := Fin.addCases w.1 w.2
  left_inv w := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  right_inv w := by
    apply Prod.ext <;> funext i <;> simp

/-- Positive levels have twice the previous complete-word length. -/
theorem completeWord_length_double (ell : ℕ) (hell : 1 ≤ ell) :
    2 ^ ((ell + 1) - 1) = 2 ^ (ell - 1) + 2 ^ (ell - 1) := by
  calc
    2 ^ ((ell + 1) - 1) = 2 ^ ell := by simp
    _ = 2 ^ ((ell - 1) + 1) := by rw [Nat.sub_add_cancel hell]
    _ = 2 ^ (ell - 1) + 2 ^ (ell - 1) := by rw [pow_succ, Nat.mul_two]

/-- The literal two-child bridge, with source level convention 2^(ell-1). -/
def completeWordSplitEquiv (ell : ℕ) (hell : 1 ≤ ell) :
    CompleteWord (ell + 1) ≃ CompleteWord ell × CompleteWord ell :=
  (Equiv.arrowCongr (finCongr (completeWord_length_double ell hell))
    (Equiv.refl (Fin 3))).trans
      (fineWordSplitEquiv (2 ^ (ell - 1)) (2 ^ (ell - 1)))

/-- Product of two full-word probability functions, on literal parent words. -/
noncomputable def concatenatedProbability {ell : ℕ} (hell : 1 ≤ ell)
    (p q : CompleteWord ell → ℝ) (w : CompleteWord (ell + 1)) : ℝ :=
  p ((completeWordSplitEquiv ell hell w).1) *
    q ((completeWordSplitEquiv ell hell w).2)

/-- A finite mixture of literal full-word probability functions. -/
noncomputable def mixedProbability {R : Type u} [Fintype R] {ell : ℕ}
    (weights : R → ℝ) (p : R → CompleteWord ell → ℝ)
    (w : CompleteWord ell) : ℝ :=
  ∑ r, weights r * p r w

end MME.CompleteSplit


