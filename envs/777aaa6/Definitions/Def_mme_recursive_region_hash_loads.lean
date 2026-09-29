-- Prove2me | Definitions.Def_mme_recursive_region_hash_loads
-- name    : mme_recursive_region_hash_loads
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-13T16:30:29.918858+00:00
-- url     : https://prove2.me/theorems/35db7606-7c46-4084-91fd-c19f8bb1f8bf
-- title:
--   Literal X/Y/Z counts defining a common regional hash scale
-- statement:
--   The X load uses the ambient degree ratio. The Y/Z loads use the target fiber, exact compatibility count and joint parent-word type-class count, restricted to the actual retained profile predicate. These definitions do not assume any quantitative budget.
-- source:
--   Quantitative finite realization for a jointly processed constituent region, connected to the physical recursive Y/Z extraction for More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 . This is a supporting lemma, not a proof of the regional asymptotic theorem or a numerical omega certificate.

import Definitions.Def_mme_common_hash_scale
import Definitions.Def_mme_recursive_yz_hash_filter

open BigOperators MME MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
namespace MME.RegionRealization

abbrev LoadIndex (half R ell : ℕ) (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ) :=
  Unit ⊕ (Fin 2 × Address half R parent n × (Position n → CompleteSplit.CompleteWord ell))

noncomputable def loadDen {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) :
    LoadIndex half R ell parent n → ℕ
  | .inl _ => max 1 ((RecursiveXHash.ambient (n := n) m).image (RecursiveXHash.block 0)).card
  | .inr (i, a, f) => Nat.card {g : Position n → CompleteSplit.CompleteWord ell //
      ParentType (RecursiveXHash.block (yzMode i) a)
        (parentCounts (RecursiveXHash.block (yzMode i) a) f) g}

noncomputable def loadNum {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (d : ℕ)
    (mu : Fin 2 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (keep : Fin 2 → Address half R parent n → (Position n → CompleteSplit.CompleteWord ell) → Prop) :
    LoadIndex half R ell parent n → ℕ
  | .inl _ => 8 * (RecursiveXHash.ambient (n := n) m).card
  | .inr (i, a, f) =>
      if a ∈ RecursiveXHash.target m ∧ f ∈ unbrokenWords htotal (yzMode i) a (mu i) ∧ keep i a f
      then 128 * d * ((RecursiveXHash.target (n := n) m).filter (fun b ↦
        RecursiveXHash.block (yzMode i) b = RecursiveXHash.block (yzMode i) a)).card *
        compatibilityNumber (yzBoundary i) (modeGroup (yzMode i)) (mu i)
      else 0

end MME.RegionRealization


