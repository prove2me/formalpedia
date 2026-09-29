-- Prove2me | Theorems.Thm_mme_recursive_region_computed_hash_selection
-- name    : mme_recursive_region_computed_hash_selection
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T16:49:51.485399+00:00
-- url     : https://prove2.me/theorems/55051987-cde2-4ee6-85c5-21d89de8ff17
-- title:
--   Actual regional hash selection from computed X/Y/Z loads
-- statement:
--   Construct the common prime, AP-free labels, affine hash state and isolated simultaneously usable family from the literal target, ambient, compatibility and parent type counts. The only analytic budget still assumed is the initial parent-type hole bound; X degree and Y/Z hash ratios are derived from the computed maximum. This is a finite selection theorem, not the full admissible-distribution realization theorem.
-- source:
--   Quantitative finite realization for a jointly processed constituent region, connected to the physical recursive Y/Z extraction for More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 . This is a supporting lemma, not a proof of the regional asymptotic theorem or a numerical omega certificate.

import Definitions.Def_mme_recursive_region_hash_loads
import Theorems.Thm_mme_common_hash_scale_realization
import Theorems.Thm_mme_recursive_yz_simultaneous_usable_isolation

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_recursive_region_computed_hash_selection {half R ell N : ℕ}
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (d : ℕ)
    (mu : Fin 2 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ i c, ∑ w, mu i c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (keep : Fin 2 → Address half R parent n → (Position n → CompleteSplit.CompleteWord ell) → Prop)
    (htype : ∀ i a, a ∈ RecursiveXHash.target m →
      8 * d * (typeHoles htotal (yzMode i) a (mu i) (keep i a)).card ≤
        (unbrokenWords htotal (yzMode i) a (mu i)).card) :
    let Q := commonScale half (loadNum htotal m d mu keep) (loadDen m)
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ half < p ∧ 2 * Q < p ∧ p ≤ 4 * Q ∧
      ∃ S : Finset ℕ, S ⊆ Finset.range (p / 2) ∧ ThreeAPFree (S : Set ℕ) ∧
      ∃ q : (Fin (N + 2) → ZMod p) × ZMod p, ∃ I : Finset (Address half R parent n),
        I ⊆ RecursiveXHash.target m ∧
        I ⊆ RecursiveXHash.bucketed m e (S.image (fun a : ℕ ↦ (a : ZMod p))) q ∧
        I ⊆ RecursiveXHash.hashed m e (S.image (fun a : ℕ ↦ (a : ZMod p))) q ∧
        I ⊆ usable htotal m e (S.image (fun a : ℕ ↦ (a : ZMod p))) q d mu keep ∧
        (∀ a ∈ I, ∀ b ∈ RecursiveXHash.bucketed m e (S.image (fun a : ℕ ↦ (a : ZMod p))) q,
          RecursiveXHash.block 0 a = RecursiveXHash.block 0 b → a = b) ∧
        ((RecursiveXHash.target (n := n) m).card : ℝ) *
          Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ (I.card : ℝ) := by sorry
