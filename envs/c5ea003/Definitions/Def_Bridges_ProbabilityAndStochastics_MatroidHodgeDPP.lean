-- Prove2me | Definitions.Def_Bridges_ProbabilityAndStochastics_MatroidHodgeDPP
-- name    : Bridges_ProbabilityAndStochastics_MatroidHodgeDPP
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:33:11.91241+00:00
-- url     : https://prove2.me/theorems/6b5268c8-7bc7-4ebe-bd73-1140004f20d4
-- title:
--   Aether Catalog definitions — Bridges_ProbabilityAndStochastics_MatroidHodgeDPP
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ProbabilityAndStochastics.MatroidHodgeDPP`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ProbabilityAndStochastics/MatroidHodgeDPP.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Matroid Hodge Theory and DPP Support Exchange

This file formalizes the connection between determinantal point processes (DPPs),
matroid theory, and Lorentzian polynomial geometry.

## Novel Definitions

* `FinsetMatroid` — Matroid structure via bases on `Finset (Fin n)` with exchange axiom
* `DPPSupport` — Support of a DPP kernel (subsets with positive principal minor)
* `SubmodularFn` — Submodularity condition for set functions
* `DPPSymmetricExchangeProperty` — The testable conjecture

## Main Results

* `finset_matroid_sym_exchange_singleton` — Symmetric exchange for singleton diff
* `psd_all_principal_minors_nonneg` — All principal minors of PSD are nonneg
* `dpp_support_size_one_characterization` — Size-1 DPP support characterization
* `rank1_kernel_psd` — Rank-1 kernels vvᵀ are PSD
* `psd_entry_cauchy_schwarz` — Cauchy-Schwarz for PSD entries
* `uniform_matroid_symmetric_exchange` — Symmetric exchange for uniform matroid
* `total_negdep_eq_frobenius` — Total negative dependence = Frobenius norm

## Cross-Domain: Matroid Theory ↔ Linear Algebra ↔ Probability ↔ Optimization
-/

open Finset BigOperators Matrix

noncomputable section

/-! ## Part I: Matroid Foundations -/

/-- A finset-based matroid on `Fin n`. Bases are nonempty families of
    equal-sized subsets satisfying the exchange axiom.
    This is a novel formalization encoding matroids via their basis collection
    on `Finset (Fin n)` with the exchange property stated combinatorially. -/
structure FinsetMatroid (n : ℕ) where
  /-- The collection of bases -/
  bases : Finset (Finset (Fin n))
  /-- Bases are nonempty -/
  bases_nonempty : bases.Nonempty
  /-- All bases have equal cardinality -/
  bases_equicard : ∀ B₁ ∈ bases, ∀ B₂ ∈ bases, B₁.card = B₂.card
  /-- Basis exchange axiom -/
  exchange : ∀ B₁ ∈ bases, ∀ B₂ ∈ bases,
    ∀ x ∈ B₁ \ B₂, ∃ y ∈ B₂ \ B₁, (B₁.erase x ∪ {y}) ∈ bases

/-- The rank of a matroid: the common cardinality of all bases. -/
def FinsetMatroid.rank {n : ℕ} (M : FinsetMatroid n) : ℕ :=
  M.bases_nonempty.choose.card


/-! ## Part II: Symmetric Exchange for Singleton Symmetric Difference

When B₁ \ B₂ = {x} and B₂ \ B₁ = {y}, the two bases differ by exactly one
element swap. The reverse swap B₂ - y + x recovers B₁. -/


/-! ## Part III: DPP Support -/

/-- The support of a DPP: subsets S of size d with det(K_S) > 0. -/
def DPPSupport {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (d : ℕ) :
    Finset (Finset (Fin n)) :=
  (Finset.univ.powerset.filter (fun S => S.card = d)).filter
    (fun S => (0 : ℝ) <
      (K.submatrix (fun i : S => i.val) (fun j : S => j.val)).det)



/-! ## Part IV: DPP Support Characterization -/




/-! ## Part V: Submodularity (Cross-Domain: Combinatorics ↔ Optimization) -/



/-! ## Part VI: Rank-1 Kernels -/

/-- A rank-1 PSD matrix vvᵀ. -/
def rank1Kernel {n : ℕ} (v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => v i * v j)


/-
A rank-1 kernel vvᵀ is PSD: xᵀ(vvᵀ)x = (vᵀx)² ≥ 0.
    Proof: rewrite xᵀ(vvᵀ)x as (∑ᵢ vᵢxᵢ)² and use sq_nonneg.
-/

/-! ## Part VII: Quantitative Negative Dependence -/

/-- The negative dependence gap for entry (i,j): K_ij · K_ji. -/
def negDepGap {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  K i j * K j i



/-! ## Part VIII: PSD Entry Cauchy-Schwarz -/

/-
Cauchy-Schwarz for PSD entries: K_ij² ≤ K_ii · K_jj.
    Proof: 2×2 principal minor det ≥ 0 gives K_ii·K_jj - K_ij² ≥ 0.
-/

/-! ## Part IX: Uniform Matroid and Symmetric Exchange -/

/-- The uniform matroid U(k,n): all k-element subsets of Fin n are bases. -/
def uniformMatroid (n k : ℕ)
    (hne : ((Finset.univ : Finset (Fin n)).powerset.filter
      (fun S => S.card = k)).Nonempty) : FinsetMatroid n where
  bases := (Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card = k)
  bases_nonempty := hne
  bases_equicard := by
    intro B₁ hB₁ B₂ hB₂
    simp only [mem_filter] at hB₁ hB₂; omega
  exchange := by
    intro B₁ hB₁ B₂ hB₂ x hx
    simp only [mem_filter, mem_powerset] at hB₁ hB₂
    have hx_mem := (mem_sdiff.mp hx).1
    have hx_nmem := (mem_sdiff.mp hx).2
    have hk_pos : 0 < B₁.card := Finset.card_pos.mpr ⟨x, hx_mem⟩
    have h_sdiff_ne : (B₂ \ B₁).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h_empty
      have h_sub := sdiff_eq_empty_iff_subset.mp h_empty
      have := Finset.eq_of_subset_of_card_le h_sub (by omega)
      subst this; exact hx_nmem hx_mem
    obtain ⟨y, hy⟩ := h_sdiff_ne
    have hy_nmem := (mem_sdiff.mp hy).2
    exact ⟨y, hy, by
      simp only [mem_filter, mem_powerset]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [card_union_of_disjoint (by
        rw [Finset.disjoint_singleton_right]
        exact fun h => hy_nmem (mem_erase.mp h).2)]
      have hk_eq : B₁.card = k := hB₁.2
      have hk_pos : 0 < k := hk_eq ▸ Finset.card_pos.mpr ⟨x, hx_mem⟩
      simp only [card_erase_of_mem hx_mem, hk_eq]
      exact Nat.sub_add_cancel hk_pos⟩

/-
Symmetric exchange for uniform matroid: swapping elements between
    two k-subsets preserves being a k-subset in both directions.
-/

/-! ## Part X: PSD Trace -/


/-! ## Part XI: Complement Identity -/


/-! ## Part XII: Testable Conjecture -/


/-- The matroid rank function: maximum |A ∩ B| over all bases B. -/
def matroidRankFn {n : ℕ} (M : FinsetMatroid n) (A : Finset (Fin n)) : ℕ :=
  Finset.sup M.bases (fun B => (A ∩ B).card)



end


