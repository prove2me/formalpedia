-- Prove2me | Definitions.Def_erdos390_floating_rounding
-- name    : erdos390_floating_rounding
-- status  : Definition
-- author  : @doctosil
-- created : 2026-09-16T13:35:23.466717+00:00
-- url     : https://prove2.me/theorems/30d5a2ce-d804-43c3-88b4-2c121c4afb5c
-- title:
--   Finite rows and incidence columns for floating rounding
-- statement:
--   For finite coordinate, row and column sets $A,R,C$, a map $r:A\to R$ and an incidence relation $I\subseteq C\times A$, define the row fiber $A_s=\{a:r(a)=s\}$, the columns containing a coordinate $C_a=\{c:(c,a)\in I\}$, and the real-valued incidence indicator $1_I(c,a)$. These provide the interface for exact row sums and bounded column discrepancy in finite floating rounding.
-- source:
--   Shouqiao Wang, A Proposed Solution to Erdos Problem 390, Section 10, floating rounding; https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/FloatingRounding.lean

import Mathlib

namespace Erdos390.WholePaper

noncomputable section

def columnsContaining {A C : Type*} [Fintype C]
    (H : Finset C) (inc : C → A → Prop) (a : A) : Finset C := by
  classical
  exact H.filter fun c ↦ inc c a

def rowSet {A R : Type*} [Fintype A]
    (row : A → R) (r : R) : Finset A := by
  classical
  exact Finset.univ.filter fun a ↦ row a = r

def zeroOneColumn {A C : Type*} (inc : C → A → Prop) (c : C) (a : A) : ℝ := by
  classical
  exact if inc c a then 1 else 0

end
end Erdos390.WholePaper


