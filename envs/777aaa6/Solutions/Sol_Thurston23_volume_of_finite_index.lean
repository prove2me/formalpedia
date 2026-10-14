-- Prove2me | solution 1 for Thurston23.volume_of_finite_index
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-10T12:07:50.409277+00:00
-- url     : https://prove2.me/submissions/a3aa25b0-e60a-4232-a694-ea9e69a1e6d4

import Mathlib
import Definitions.Def_Thurston23_bundle

/-!
Passing to a subgroup of index `n` multiplies the volume of a fundamental
domain by `n`.

The proof is the classical coset computation.  Writing `F` for a fundamental
domain of `G` and `FH` for one of `H`, the measure of `FH` is expanded as a sum
over `G` of the pieces `g • FH ∩ F`; grouping `g` by left cosets of `H` turns
the inner sum over `H` into the measure of a single translate of `F`, and the
outer sum then has one term `μ F` for each of the `H.index` cosets.
-/

namespace VolumeFiniteIndexAux

open MeasureTheory Set Pointwise TopologicalSpace

variable {G : Type*} [Group G]

/-- Explicit coset decomposition `(G ⧸ H) × H ≃ G`, sending `(q, h)` to
`(Quotient.out q) * h`. -/
noncomputable def cosetProdEquiv (H : Subgroup G) : (G ⧸ H) × H ≃ G where
  toFun p := (Quotient.out p.1) * (p.2 : G)
  invFun g := (QuotientGroup.mk g,
    ⟨(Quotient.out (QuotientGroup.mk g : G ⧸ H))⁻¹ * g, by
      have h : ((Quotient.out (QuotientGroup.mk g : G ⧸ H) : G) : G ⧸ H)
          = (QuotientGroup.mk g : G ⧸ H) := Quotient.out_eq _
      exact QuotientGroup.eq.mp h⟩)
  left_inv := by
    rintro ⟨q, h, hh⟩
    have hq : (QuotientGroup.mk ((Quotient.out q) * h) : G ⧸ H) = q := by
      rw [QuotientGroup.mk_mul_of_mem _ hh]; simp
    ext
    · exact hq
    · simp only [hq]
      group
  right_inv := by
    intro g
    simp only
    group

/-- A fundamental domain for a finite-index subgroup has `index` times the
measure of a fundamental domain for the whole group. -/
theorem measure_fd_subgroup {α : Type*} [MeasurableSpace α] [MulAction G α]
    [Countable G] [MeasurableConstSMul G α]
    {μ : Measure α} [SMulInvariantMeasure G α μ]
    (H : Subgroup G) (hH : 0 < H.index)
    {F FH : Set α} (hF : IsFundamentalDomain G F μ) (hFH : IsFundamentalDomain H FH μ) :
    μ FH = H.index • μ F := by
  classical
  have _ : MeasurableConstSMul H α := ⟨fun h => measurable_const_smul (h : G)⟩
  have _ : Countable H := Subtype.countable
  have hfin : Finite (G ⧸ H) :=
    Nat.finite_of_card_ne_zero (by simpa [Subgroup.index] using hH.ne')
  have _ : Fintype (G ⧸ H) := Fintype.ofFinite _
  -- Along one coset the sum over `H` rebuilds a single translate of `F`.
  have key : ∀ q : G ⧸ H,
      ∑' h : H, μ ((Quotient.out q * (h : G)) • FH ∩ F) = μ F := by
    intro q
    calc ∑' h : H, μ ((Quotient.out q * (h : G)) • FH ∩ F)
        = ∑' h : H, μ ((Quotient.out q)⁻¹ • F ∩ (h : G) • FH) := by
          refine tsum_congr fun h => ?_
          rw [mul_smul, ← measure_inter_inv_smul, Set.inter_comm]
      _ = μ ((Quotient.out q)⁻¹ • F) := (hFH.measure_eq_tsum' _).symm
      _ = μ F := measure_smul _ _ _
  rw [hF.measure_eq_tsum FH, ← (cosetProdEquiv H).tsum_eq, ENNReal.tsum_prod']
  simp only [cosetProdEquiv, Equiv.coe_fn_mk]
  rw [tsum_congr key, tsum_fintype, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card]
  rfl

end VolumeFiniteIndexAux

open MeasureTheory Set TopologicalSpace Thurston23 in
theorem solution {G : Type} [Group G] [MulAction G H3]
    (hG : IsKleinian G) (H : Subgroup G) (hH : 0 < H.index)
    (F FH : Set H3) (hF : MeasureTheory.IsFundamentalDomain G F hvol)
    (hFH : MeasureTheory.IsFundamentalDomain H FH hvol) :
    hvol FH = H.index • hvol F := by
  -- `H3` is an open subset of `ℝ³`, hence locally compact, hence σ-compact.
  have _ : LocallyCompactSpace H3 :=
    (isOpen_lt continuous_const (continuous_apply 2)).locallyCompactSpace
  -- A properly discontinuous action on a σ-compact space is by a countable group.
  have _ : Countable G := by
    have p₀ : H3 := ⟨fun _ => (1 : ℝ), by norm_num⟩
    have hcnt : ∀ n : ℕ, ({g : G |
        ((fun p : H3 => g • p) '' (compactCovering H3 n) ∩ compactCovering H3 n).Nonempty
        }).Countable :=
      fun n => (hG.properly_discontinuous _ (isCompact_compactCovering _ n)).countable
    have huniv : (Set.univ : Set G) ⊆ ⋃ n, {g : G |
        ((fun p : H3 => g • p) '' (compactCovering H3 n) ∩ compactCovering H3 n).Nonempty} := by
      intro g _
      obtain ⟨n, hn⟩ := exists_mem_compactCovering p₀
      obtain ⟨m, hm⟩ := exists_mem_compactCovering (g • p₀)
      exact Set.mem_iUnion.2 ⟨max n m,
        ⟨g • p₀, ⟨p₀, compactCovering_subset _ (le_max_left n m) hn, rfl⟩,
          compactCovering_subset _ (le_max_right n m) hm⟩⟩
    exact Set.countable_univ_iff.mp ((Set.countable_iUnion hcnt).mono huniv)
  have _ : MeasurableConstSMul G H3 := ⟨fun g => (hG.measure_preserving g).measurable⟩
  have _ : SMulInvariantMeasure G H3 hvol :=
    ⟨fun g s hs => (hG.measure_preserving g).measure_preimage hs.nullMeasurableSet⟩
  exact VolumeFiniteIndexAux.measure_fd_subgroup H hH hF hFH
