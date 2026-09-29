-- Prove2me | Theorems.Thm_mme_recursive_yz_simultaneous_usable_isolation
-- name    : mme_recursive_yz_simultaneous_usable_isolation
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-12T11:00:40.800343+00:00
-- url     : https://prove2.me/theorems/e9f826bb-3bac-46e5-b599-b222c32efa4b
-- title:
--   Simultaneous X isolation and Y/Z usability at one physical hash state
-- statement:
--   For a recursive split type, suppose the X degree budget holds, each initial Y/Z type filter removes at most $1/(8d)$ of its unbroken words, and every passing fine word satisfies the exact compatibility-to-parent-type modulus budget with constant $128d$. Then one physical affine hash state admits a selected family $I$ of target addresses, all retained by both descriptions of the same AP-free hash, all usable in Y and Z, and X-isolated against the entire retained ambient family. Its size satisfies $$|I|\ge |T||S|/(2p^2).$$ This is a simultaneous selection result: the copy-wise Y/Z hole bounds and X isolation hold in the same state.
-- source:
--   Finite recursive extraction in Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 6.3--6.5; https://arxiv.org/html/2404.16349v2.

import Theorems.Thm_mme_recursive_yz_simultaneous_usable_incidence
import Theorems.Thm_mme_recursive_x_hash_finite_usable_isolation
open BigOperators MME MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem mme_recursive_yz_simultaneous_usable_isolation {half R ell N p : ℕ} [Fact p.Prime]
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (hpodd : Odd p) (hgrade : half < p) (d : ℕ)
    (mu : Fin 2 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ i c, ∑ w, mu i c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (keep : Fin 2 → Address half R parent n →
      (Position n → CompleteSplit.CompleteWord ell) → Prop)
    (htype : ∀ i a, a ∈ RecursiveXHash.target m →
      8 * d * (typeHoles htotal (yzMode i) a (mu i) (keep i a)).card ≤
        (unbrokenWords htotal (yzMode i) a (mu i)).card)
    (hbudget : ∀ i a, a ∈ RecursiveXHash.target m →
      ∀ f ∈ unbrokenWords htotal (yzMode i) a (mu i), keep i a f →
        128 * d * ((RecursiveXHash.target (n := n) m).filter (fun b ↦
          RecursiveXHash.block (yzMode i) b = RecursiveXHash.block (yzMode i) a)).card *
            compatibilityNumber (yzBoundary i) (modeGroup (yzMode i)) (mu i) ≤
          p * Nat.card {g : Position n → CompleteSplit.CompleteWord ell //
            ParentType (RecursiveXHash.block (yzMode i) a)
              (parentCounts (RecursiveXHash.block (yzMode i) a) f) g})
    (hxBudget : 8 * (RecursiveXHash.ambient (n := n) m).card ≤
      p * ((RecursiveXHash.ambient (n := n) m).image (RecursiveXHash.block 0)).card) :
    let castS := S.image (fun a : ℕ ↦ (a : ZMod p))
    ∃ q : (Fin (N + 2) → ZMod p) × ZMod p, ∃ I : Finset (Address half R parent n),
      I ⊆ RecursiveXHash.target m ∧
      I ⊆ RecursiveXHash.bucketed m e castS q ∧
      I ⊆ RecursiveXHash.hashed m e castS q ∧
      I ⊆ usable htotal m e castS q d mu keep ∧
      (∀ a ∈ I, ∀ b ∈ RecursiveXHash.bucketed m e castS q,
        RecursiveXHash.block 0 a = RecursiveXHash.block 0 b → a = b) ∧
      ((RecursiveXHash.target (n := n) m).card : ℝ) * S.card / (2 * (p : ℝ) ^ 2) ≤ (I.card : ℝ)  := by sorry
