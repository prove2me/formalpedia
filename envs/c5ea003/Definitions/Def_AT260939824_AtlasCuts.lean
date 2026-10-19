-- Prove2me | Definitions.Def_AT260939824_AtlasCuts
-- name    : AT260939824_AtlasCuts
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:40:46.989995+00:00
-- url     : https://prove2.me/theorems/c691b1f7-b08b-4244-acbc-2bc14dee2d7b
-- title:
--   Finite forbidden sets for separated integer cuts
-- statement:
--   For a finite set $E\subseteq\mathbb Z$ of earlier cuts and an integer radius $\delta\ge0$, define
--
--   $$ \operatorname{Forbidden}(E,\delta)=\bigcup_{b\in E}([b-\delta,b+\delta]\cap\mathbb Z). $$
--
--   Its size is at most $|E|(2\delta+1)$. For $P\ge1$, $L\ge32P$, and $|E|\le2P$, the cut-selection interface supplies an integer in $[a,a+L]$ at distance greater than $\lfloor L/(16P)\rfloor$ from every earlier cut. This controls subdivision spacing.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 3; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/AtlasCuts.lean, selected declaration lines 19-20, 22-33, 35-38, 40-72; SHA-256 d89ab37e01b7ddc3118cccffe43ae0137c9cfc7c57d65429085aaa9376695225. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Init
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# The finite cut-selection argument in Lemma 3.2

The earlier parallel cuts exclude a controlled number of integer
candidates. This module proves the actual separated-cut existence with
the paper's constants. It does not assume the rectangular atlas.
-/

namespace AbelianTargets

open scoped BigOperators

def forbiddenCuts (earlier : Finset ℤ) (δ : ℕ) : Finset ℤ :=
  earlier.biUnion (fun b => Finset.Icc (b-(δ : ℤ)) (b+δ))

theorem forbiddenCuts_card_le (earlier : Finset ℤ) (δ : ℕ) :
    (forbiddenCuts earlier δ).card ≤ earlier.card * (2*δ+1) := by
  unfold forbiddenCuts
  calc
    _ ≤ ∑ b ∈ earlier, (Finset.Icc (b-(δ : ℤ)) (b+δ)).card := Finset.card_biUnion_le
    _ = earlier.card * (2*δ+1) := by
      have hcard : ∀ b : ℤ, (Finset.Icc (b-(δ : ℤ)) (b+δ)).card = 2*δ+1 := by
        intro b
        rw [Int.card_Icc]
        have he : b+(δ : ℤ)+1-(b-δ) = ((2*δ+1 : ℕ) : ℤ) := by push_cast; ring
        rw [he, Int.toNat_natCast]
      simp [hcard, nsmul_eq_mul]

theorem cut_budget_strict {P L : ℕ} (hP : 1 ≤ P) (hL : 32*P ≤ L) :
    2*P*(2*(L/(16*P))+1) < L+1 := by
  have hdiv := Nat.mul_div_le L (16*P)
  nlinarith

/-- An integer candidate separated from every earlier cut. The stronger
strict separation here is enough for the non-strict bound in the paper. -/
theorem exists_separated_cut {P L : ℕ} (hP : 1 ≤ P) (hL : 32*P ≤ L)
    (a : ℤ) (earlier : Finset ℤ) (hearlier : earlier.card ≤ 2*P) :
    ∃ c : ℤ, a ≤ c ∧ c ≤ a+L ∧
      ∀ b ∈ earlier, ((L/(16*P) : ℕ) : ℤ) < |c-b| := by
  let δ := L/(16*P)
  let candidates := Finset.Icc a (a+(L : ℤ))
  have hcard : candidates.card = L+1 := by
    dsimp [candidates]
    rw [Int.card_Icc]
    have he : a+(L : ℤ)+1-a = ((L+1 : ℕ) : ℤ) := by push_cast; ring
    rw [he, Int.toNat_natCast]
  have hbad : (forbiddenCuts earlier δ).card < candidates.card := by
    rw [hcard]
    exact ((forbiddenCuts_card_le earlier δ).trans
      (Nat.mul_le_mul_right (2*δ+1) hearlier)).trans_lt (cut_budget_strict hP hL)
  have hnsubset : ¬candidates ⊆ forbiddenCuts earlier δ := by
    intro hs
    have := Finset.card_le_card hs
    omega
  obtain ⟨c,hc,hnot⟩ := Finset.not_subset.mp hnsubset
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hc
  refine ⟨c,hlo,hhi,?_⟩
  intro b hb
  have hnotIcc : c ∉ Finset.Icc (b-(δ : ℤ)) (b+δ) := by
    intro hc'
    exact hnot (Finset.mem_biUnion.mpr ⟨b,hb,hc'⟩)
  have hnotbetween : ¬(b-(δ : ℤ) ≤ c ∧ c ≤ b+δ) := by
    simpa only [Finset.mem_Icc] using hnotIcc
  change (δ : ℤ) < |c-b|
  rw [lt_abs]
  omega



end AbelianTargets


