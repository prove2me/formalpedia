-- Prove2me | Theorems.Thm_mme_recursive_yz_nonhole_implies_owned
-- name    : mme_recursive_yz_nonhole_implies_owned
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-12T11:03:28.185028+00:00
-- url     : https://prove2.me/theorems/e6aeec42-4eeb-45f1-aebf-473cd7ccf453
-- title:
--   Actual Y/Z nonholes have unique ownership among selected copies
-- statement:
--   Consider an injectively indexed family of retained target addresses and a full fine-word block useful at one selected address. If the block lies outside the actual Y or Z type-filter and collision holes, then it satisfies the owned-copy filter: it is graded, useful, and compatible with no other selected address. No separate coarse-word equality or ownership assumption is required.
--
--   The conclusion identifies the nonholes counted by the loss theorem with the basis labels retained by the concrete CW extraction theorem.
-- source:
--   Finite recursive extraction in Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 6.3--6.5; https://arxiv.org/html/2404.16349v2.

import Definitions.Def_mme_recursive_yz_hash_filter
open BigOperators MME MME.RecursiveYZ MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem mme_recursive_yz_nonhole_implies_owned {half R ell k N p : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (S : Finset (ZMod p))
    (state : (Fin (N + 2) → ZMod p) × ZMod p)
    (address : Fin k → Address half R parent n) (hinj : Function.Injective address)
    (hT : ∀ j, address j ∈ RecursiveXHash.target m)
    (hHash : ∀ j, address j ∈ RecursiveXHash.hashed m e S state)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ)
    (i : Fin 2) (j : Fin k) (keep : (Position n → CompleteWord ell) → Prop)
    (f : Position n → CompleteWord ell)
    (hf : f ∈ unbrokenWords htotal (yzMode i) (address j) (mu (yzMode i)))
    (hn : f ∉ filterHoles htotal m e S state i (mu (yzMode i)) (address j) keep) :
    Owned htotal address mu j (yzMode i) f  := by sorry
