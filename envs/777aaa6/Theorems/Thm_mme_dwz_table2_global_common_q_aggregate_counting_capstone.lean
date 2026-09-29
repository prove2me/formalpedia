-- Prove2me | Theorems.Thm_mme_dwz_table2_global_common_q_aggregate_counting_capstone
-- name    : mme_dwz_table2_global_common_q_aggregate_counting_capstone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T09:03:10.149903+00:00
-- url     : https://prove2.me/theorems/afc0b4e9-c6c1-4c6f-b8a2-96ed7796526b
-- title:
--   A common affine state with exact-profile aggregate source mass
-- statement:
--   For all sufficiently large Table-2 scaling parameters m, there exist one odd common prime p, one lower-half three-term-progression-free set S, one common affine state q, and an enumerated exact-profile family of source words with the complete DWZ bucket and isolation certificates. The enumeration preserves every prescribed fifteen-cell profile and its supported mixed triples have a common X/Y owner. Moreover,
--
--   $$\frac{\binom{L}{(c_s)_{s\in[15]}}\,|S|}{2p^2}\leq\sum_r \eta_r,$$
--
--   where each c_s is the prescribed Table-2 component multiplicity and η_r is the nonhole fraction of the common-state broken copy for the r-th retained owner. The statement also retains the ambient marginal family, the selected finset, the common state, the enumeration, the collision degree, prime bounds, coarse-Z factorization, and bucket/isolation witnesses so that the subsequent tensor restriction uses the same certificate.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 6.1, Equation (21), and Claim 6.8.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_hole_cover_data
import Definitions.Def_mme_dwz_global_common_state_broken_copy

open MME BigOperators Filter
open MME.DWZSquare

set_option autoImplicit false

/-!
# Quantitative common-state capstone (tensor-free statement draft)

This matches every non-tensor conjunct of the raw source leaf.  The affine
dimension is fixed canonically to `N = L - 1`.  It deliberately retains the
ambient marginal family, the selected exact-profile finset, and all of the
canonical-bucket certificates for the *same* `q` and enumeration.  Thus a
later tensor theorem can consume the witnesses without trying to recover
bucket/isolation data hidden behind an existential.
-/

theorem mme_dwz_table2_global_common_q_aggregate_counting_capstone :
    ∀ᶠ m : ℕ in atTop,
      let L : ℕ := MME.DWZTable2Counts.scale * m
      let N : ℕ := L - 1
      let alphaX : Fin 5 → ℕ := fun x ↦
        ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
          MME.DWZTable2Counts.component s.1 * m
      let alphaY : Fin 5 → ℕ := fun y ↦
        ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
          MME.DWZTable2Counts.component s.1 * m
      let alphaZ : Fin 5 → ℕ := fun z ↦
        MME.DWZTable2Counts.alphaZ z * m
      let ExactProfile : (Fin (N + 1) → Fin 15) → Prop := fun a ↦
        ∀ s, Fintype.card {t : Fin (N + 1) // a t = s} =
          MME.DWZTable2Counts.component s * m
      ∃ (n p fixedTargetCard d Q : ℕ)
          (R : ℝ) (S : Finset ℕ)
          (base : Fin L → Fin 15)
          (reindex : Fin (N + 1) ≃ Fin L)
          (q : (Fin (N + 2) → ZMod p) × ZMod p)
          (A I : Finset (Fin (N + 1) → Fin 15))
          (edge : Fin n → Fin (N + 1) → Fin 15),
        0 < m ∧
        2 ≤ p ∧
        p.Prime ∧ Odd p ∧ 4 < p ∧
        (∀ s,
          Fintype.card {t : Fin L // base t = s} =
            MME.DWZTable2Counts.component s * m) ∧
        fixedTargetCard = Nat.card
          {w : Fin L → Fin 15 //
            (∀ t, MME.DWZSquare.shapeZ (w t) =
              MME.DWZSquare.shapeZ (base t)) ∧
            ∀ s, Fintype.card {t : Fin L // w t = s} =
              MME.DWZTable2Counts.component s * m} ∧
        Nat.multinomial Finset.univ
              (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) =
            Nat.multinomial Finset.univ
                (fun k : Fin 5 ↦ MME.DWZTable2Counts.alphaZ k * m) *
              fixedTargetCard ∧
        0 < d ∧
        (d : ℝ) ≤
          (6 * (((L + 1 : ℕ) : ℝ))) ^ 5 *
            (((L + 1 : ℕ) : ℝ)) ^ 15 *
            Real.exp
              ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
                (MME.DWZSquare.maxSameMarginalEntropy -
                  mme_modern_entropyBits
                    (mme_modern_marginal MME.DWZSquare.shapeX
                      MME.DWZSquare.alpha))) ∧
        R =
          (6 * (((L + 1 : ℕ) : ℝ))) ^ 9 *
            (fixedTargetCard : ℝ) *
            Real.exp
              ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
                MME.DWZSquare.logAlphaP) ∧
        (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R) ∧
        d ≤ 15 ^ L ∧
        Q ≤ 15 ^ L ∧
        p ≤ 2 * max 4 (8 * max d Q) ∧
        S ⊆ Finset.range (p / 2) ∧
        ThreeAPFree (S : Set ℕ) ∧
        ((p / 2 : ℕ) : ℝ) *
              Real.exp (-4 * Real.sqrt
                (Real.log (((p / 2 : ℕ) : ℝ)))) ≤
            (S.card : ℝ) ∧
        (∀ a, a ∈ A ↔
          (∀ x, Fintype.card
              {t : Fin (N + 1) //
                MME.DWZSquare.shapeX (a t) = x} = alphaX x) ∧
          (∀ y, Fintype.card
              {t : Fin (N + 1) //
                MME.DWZSquare.shapeY (a t) = y} = alphaY y) ∧
          ∀ z, Fintype.card
              {t : Fin (N + 1) //
                MME.DWZSquare.shapeZ (a t) = z} = alphaZ z) ∧
        I ⊆ A.filter ExactProfile ∧
        I ⊆ MME.dwzTable2AffineHashBucket S A q ∧
        (∀ e ∈ I,
          ∀ e' ∈ MME.dwzTable2AffineHashBucket S A q,
            (fun t ↦ MME.DWZSquare.shapeX (e t)) =
                (fun t ↦ MME.DWZSquare.shapeX (e' t)) ∨
              (fun t ↦ MME.DWZSquare.shapeY (e t)) =
                (fun t ↦ MME.DWZSquare.shapeY (e' t)) →
            e = e') ∧
        I.card = n ∧
        Function.Injective edge ∧
        Finset.univ.image edge = I ∧
        (∀ r, edge r ∈ MME.dwzTable2AffineHashBucket S A q) ∧
        (∀ r s,
          Fintype.card
              {t : Fin L //
                MME.DWZGlobalCorrelated.sourceWord reindex edge r t = s} =
            MME.DWZTable2Counts.component s * m) ∧
        (∀ js : Fin 3 → Fin n,
          (∀ t : Fin (N + 1),
            (MME.DWZSquare.shapeX (edge (js 0) t)).val +
              (MME.DWZSquare.shapeY (edge (js 1) t)).val +
              (MME.DWZSquare.shapeZ (edge (js 2) t)).val = 4) →
          js 0 = js 1) ∧
        ((Nat.multinomial Finset.univ
              (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) : ℝ) *
            (S.card : ℝ)) /
            (2 * (p : ℝ) ^ 2) ≤
          ∑ r, MME.DWZSquare.nonholeFraction
            (MME.DWZGlobalCorrelated.commonStateBrokenCopy
              m reindex q edge r) := by
  sorry
