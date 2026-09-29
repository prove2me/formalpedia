-- Prove2me | Theorems.Thm_mme_recursive_yz_simultaneous_usable_incidence
-- name    : mme_recursive_yz_simultaneous_usable_incidence
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-12T10:41:17.144247+00:00
-- url     : https://prove2.me/theorems/0f04cac2-0b7e-4d92-9921-c7dbb0f02a25
-- title:
--   Recursive Y/Z filtering: simultaneous seven-eighths usable incidence
-- statement:
--   Use the physical recursive affine hash over an odd prime $p$ exceeding the child grade, with common-label set $S$. For each target address and each of Y and Z, let $U_i$ be its actual graded, exact-profile unbroken fine blocks. Apply an arbitrary type filter, and then remove surviving blocks that are compatible with a distinct target address retained by the same hash.
--
--   Fix a repair parameter $d$. Assume the type filter removes at most $|U_i|/(8d)$ blocks, stated without division as $8d|H_i^{\rm type}|\le |U_i|$. For every block passing that filter assume the explicit finite modulus budget
--
--   $$128d\,|T_y|Q_i\le pD_f,$$
--
--   where $T_y$ counts exact-profile targets sharing its selected coarse word, $Q_i$ is the proved two-half compatibility count, and $D_f$ is the full joint-parent type-class size of that very block.
--
--   Call a target usable in a hash state when both its Y and Z total hole sets have size at most $|U_i|/(4d)$. Then
--
--   $$\sum_s |T\cap E_s\cap G_s|\ge \frac78 |T||S|p^{N+1}.$$
--
--   Thus the simultaneous $7/8$ usability premise used by the finite X-isolation selector follows from actual type-hole cardinalities and finite multinomial/type-class modulus budgets. The two mode losses are counted in the same hash state. The theorem does not assert these finite budgets for the paper's numerical witness; establishing their cofinal asymptotic versions remains an analytic/profile task.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Claim 6.21 and the simultaneous filtering/Hole Lemma step in Section 6.5; https://arxiv.org/html/2404.16349v2#S6.SS5. Explicit finite constants are a conservative formalization of the source argument.

import Definitions.Def_mme_recursive_yz_hash_filter
open BigOperators MME MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false

theorem mme_recursive_yz_simultaneous_usable_incidence {half R ell N p : ℕ} [Fact p.Prime]
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (S : Finset (ZMod p))
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
              (parentCounts (RecursiveXHash.block (yzMode i) a) f) g}) :
    7 * (RecursiveXHash.target (n := n) m).card * S.card * p ^ (N + 1) ≤
      8 * ∑ q : (Fin (N + 2) → ZMod p) × ZMod p,
        (((RecursiveXHash.target m).filter (fun a ↦ a ∈ RecursiveXHash.hashed m e S q)) ∩
          usable htotal m e S q d mu keep).card := by sorry
