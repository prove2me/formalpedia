-- Prove2me | Theorems.Thm_mme_recursive_yz_hash_ambiguity_bound
-- name    : mme_recursive_yz_hash_ambiguity_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-12T10:31:23.111807+00:00
-- url     : https://prove2.me/theorems/7f5bc619-e9c6-4796-9750-e6f23a4c4f5b
-- title:
--   Recursive Y/Z filtering: hash-state ambiguity bound
-- statement:
--   Fix an exact-profile recursive target address $a$, a prime modulus $p$ larger than every child grade, and one of the modes Y or Z. Use the physical asymmetric affine hashes with a finite common-label set $S$, on $N+1$ parent positions.
--
--   Let $f$ have fixed joint full-parent type $\eta$ over the selected coarse-mode word of $a$. Let $D$ be that joint type-class size, let $T_y$ be the target addresses sharing the coarse-mode word, and let $Q$ be the exact two-half compatibility count. Count hash states in which $a$ survives and some distinct compatible target address sharing its selected mode also survives. Their number $B$ satisfies
--
--   $$B D \le |T_y|\,Q\,|S|\,p^N.$$
--
--   The bound uses the actual common-label affine retention event. Together with the single-address count $|S|p^{N+1}$ (for odd $p$), it gives the conditional collision bound $|T_y|Q/(Dp)$. The Y and Z cases use their respective proved affine-hash pair bounds. This is the finite form of the hash-loss step in Claim 6.21; it does not assume a collision-probability estimate.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Claim 6.21 and Claims 6.18--6.20; https://arxiv.org/html/2404.16349v2#S6.SS5.

import Definitions.Def_mme_recursive_yz_physical_words
import Definitions.Def_mme_recursive_x_hash_families
open BigOperators MME MME.RecursiveXHash MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false

theorem mme_recursive_yz_hash_ambiguity_bound {half R N p : ℕ} [Fact p.Prime]
    {W G : Type*} [Fintype W] [Fintype G]
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (S : Finset (ZMod p))
    (hgrade : half < p) (i : Fin 3) (hi : i = 1 ∨ i = 2)
    (a : MME.RecursiveYZ.Address half R parent n) (ha : a ∈ target m)
    (eta : Fin R → Fin (half + 1) → (Fin 2 → W) → ℕ)
    (boundary : Cell half R parent → Prop) (group : Cell half R parent → G)
    (mu : Cell half R parent → W → ℕ)
    (hmass : ∀ c, ∑ w, mu c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (f : Position n → W) (hf : ParentType (block i a) eta f) :
    (Finset.univ.filter (fun q : (Fin (N + 2) → ZMod p) × ZMod p ↦
      a ∈ hashed m e S q ∧ ∃ b ∈ target m,
        block i b = block i a ∧ Compatible (fullCell htotal b) boundary group mu f ∧
          b ≠ a ∧ b ∈ hashed m e S q)).card *
      Nat.card {g : Position n → W // ParentType (block i a) eta g} ≤
    ((target (n := n) m).filter (fun b ↦ block i b = block i a)).card *
      compatibilityNumber boundary group mu * S.card * p ^ N := by sorry
