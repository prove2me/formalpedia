-- Prove2me | Definitions.Def_mme_recursive_yz_compatibility
-- name    : mme_recursive_yz_compatibility
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-12T10:07:13.284611+00:00
-- url     : https://prove2.me/theorems/8a9ce001-1842-4b87-9158-17ed4449579d
-- title:
--   Recursive Y/Z compatibility and exact histogram counts
-- statement:
--   For a finite set of positions partitioned into coarse cells, usefulness fixes the full fine-word histogram in every cell. Compatibility fixes each boundary cell separately and fixes only the aggregate histogram over cells with the same retained coarse-mode label. The associated partition has individual boundary cells and one merged interior cell per coarse-mode label.
--
--   For integer cell histograms $\mu$, define the exact multinomial count $\prod_c (\sum_w\mu(c,w))!/\prod_w\mu(c,w)!$. Applying this formula to the boundary/interior partition defines the compatibility count. These are concrete finite counting predicates for the recursive Y and Z filters; no loss bound or tensor restriction is assumed in the definitions.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definitions 6.8, 6.10, 6.11 and Claims 6.18--6.20; https://arxiv.org/html/2404.16349v2#S6.SS3. These are exact finite-count formalizations; the paper writes normalized profiles and asymptotic entropy bounds.

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Multinomial

open BigOperators
set_option autoImplicit false

namespace MME.RecursiveYZ

/-- The number of occurrences of a full fine word in one coarse cell. -/
noncomputable def count {P C W : Type*} [Fintype P]
    (cell : P → C) (f : P → W) (c : C) (w : W) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p ↦ cell p = c ∧ f p = w)).card

/-- Exact usefulness keeps the full joint cell histogram. -/
noncomputable def Useful {P C W : Type*} [Fintype P]
    (cell : P → C) (mu : C → W → ℕ) (f : P → W) : Prop :=
  ∀ c w, count cell f c w = mu c w

/-- Compatibility fixes individual boundary cells and aggregates all cells
sharing the retained coarse mode and parent component. -/
noncomputable def Compatible {P C W G : Type*} [Fintype P] [Fintype C]
    (cell : P → C) (boundary : C → Prop) (group : C → G)
    (mu : C → W → ℕ) (f : P → W) : Prop := by
  classical
  exact (∀ c, boundary c → ∀ w, count cell f c w = mu c w) ∧
    ∀ g w, count (group ∘ cell) f g w = ∑ c, if group c = g then mu c w else 0

/-- Partition into individual boundary cells and merged interior cells,
corresponding to Claim 6.19 and its Z analogue. -/
noncomputable def part {C G : Type*} (boundary : C → Prop) (group : C → G)
    (c : C) : {c : C // boundary c} ⊕ G := by
  classical
  exact if h : boundary c then Sum.inl ⟨c,h⟩ else Sum.inr (group c)

noncomputable def partCount {C W G : Type*} [Fintype C]
    (boundary : C → Prop) (group : C → G) (mu : C → W → ℕ)
    (s : {c : C // boundary c} ⊕ G) (w : W) : ℕ := by
  classical
  exact match s with
    | Sum.inl c => mu c w
    | Sum.inr g => ∑ c, if ¬ boundary c ∧ group c = g then mu c w else 0

/-- Exact multinomial count for words with a specified histogram in each cell. -/
noncomputable def histogramNumber {C W : Type*} [Fintype C] [Fintype W]
    (mu : C → W → ℕ) : ℕ :=
  ∏ c, (∑ w, mu c w).factorial / ∏ w, (mu c w).factorial

/-- The exact compatibility count after partitioning boundary and interior cells. -/
noncomputable def compatibilityNumber {C W G : Type*}
    [Fintype C] [Fintype W] [Fintype G]
    (boundary : C → Prop) (group : C → G) (mu : C → W → ℕ) : ℕ := by
  classical
  exact histogramNumber (partCount boundary group mu)

end MME.RecursiveYZ


