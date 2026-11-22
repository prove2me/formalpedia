-- Prove2me | Theorems.Thm_monotone_le_cauchySeq_iff_disjoint_tendsto_zero
-- name    : monotone_le_cauchySeq_iff_disjoint_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:15:34.197192+00:00
-- url     : https://prove2.me/theorems/49c409d2-5e98-4511-b52f-b36320356788
-- title:
--   monotone le cauchy Seq iff disjoint tendsto zero: monotone le cauchy Seq iff disjoint tendsto zero
-- statement:
--   For a normed vector lattice, increasing sequences bounded by `x` are
--   norm-Cauchy iff disjoint sequences in `[0, x]` converge to zero in norm.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/MeyerNieberg.lean#L704-L711
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/MeyerNieberg.lean#L704-L711

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Nakano
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_MeyerNieberg
set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [NormedVectorLattice E]

theorem monotone_le_cauchySeq_iff_disjoint_tendsto_zero {x : E} (hx : 0 ≤ x) :
    (∀ {u : ℕ → E}, (∀ n, 0 ≤ u n) → Monotone u → (∀ n, u n ≤ x) →
      CauchySeq u) ↔
    (∀ {u : ℕ → E}, (∀ n, u n ∈ Set.Icc (0 : E) x) →
      Pairwise (fun n m => IsVLDisjoint (u n) (u m)) →
      Filter.Tendsto u Filter.atTop (nhds 0)) := by sorry
