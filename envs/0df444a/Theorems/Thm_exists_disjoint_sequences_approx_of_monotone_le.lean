-- Prove2me | Theorems.Thm_exists_disjoint_sequences_approx_of_monotone_le
-- name    : exists_disjoint_sequences_approx_of_monotone_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:15:34.007589+00:00
-- url     : https://prove2.me/theorems/97c17d24-0b64-473f-a227-37745f8e56b1
-- title:
--   exists disjoint sequences approx of monotone le: exists disjoint sequences approx of monotone le
-- statement:
--   Disjointification of increments of an increasing order-bounded sequence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/MeyerNieberg.lean#L448-L517
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/MeyerNieberg.lean#L448-L517

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Nakano
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_MeyerNieberg
set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [VectorLattice E]

theorem exists_disjoint_sequences_approx_of_monotone_le {x : E} {u : ℕ → E}
    (h0 : ∀ n, 0 ≤ u n) (hmono : Monotone u) (hle : ∀ n, u n ≤ x)
    {k : ℕ} (hk : 0 < k) :
    ∃ y : Fin k → ℕ → E,
      (∀ i, Pairwise fun n m => IsVLDisjoint (y i n) (y i m)) ∧
      (∀ i n, y i n ∈ Set.Icc (0 : E) x) ∧
      ∀ n, (∑ i : Fin k, y i n) ≤ u (n + 1) - u n ∧
        u (n + 1) - u n ≤
          (∑ i : Fin k, y i n) + ((2 : ℝ) / ((k : ℝ) + 3)) • x := by sorry
