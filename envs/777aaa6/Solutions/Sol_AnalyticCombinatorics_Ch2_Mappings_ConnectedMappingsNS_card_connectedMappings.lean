-- Prove2me | solution 1 for AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS.card_connectedMappings
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:43:44.90844+00:00
-- url     : https://prove2.me/submissions/9b6d5d53-7a0a-4d7c-909a-aab8fcfe9321

import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_ForestCountComplete
import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_ConnectedMappings
import Mathlib

namespace AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS end AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Rooted forests with a specified root set

This file records the functional formulation of rooted labelled forests used in
Flajolet--Sedgewick, Chapter II: a forest rooted at a specified set `R` is a
parent map from non-roots to all vertices whose `step`-orbits are absorbed by
`R`.

The full Cayley--Pollak count is

`# rootedForests R = |R| * n ^ (n - |R| - 1)` for `0 < |R| < n`,

with the separate all-roots case equal to `1`.  The file proves the faithful
definitions, the all-roots and one-non-root cases, the total number of parent
maps, and the Abel/binomial identity that is the algebraic core of the standard
depth-one recurrence proof.
-/

open scoped BigOperators

namespace AnalyticCombinatorics.Ch2.Mappings.ForestCountNS

noncomputable section

/-- If every vertex is a root, the empty parent map is the unique forest. -/
theorem card_rootedForests_all_roots {n : ℕ} (R : Finset (Fin n))
    (hR : R = Finset.univ) :
    @Fintype.card (RootedForests R) (rootedForestsFintype R) = 1 := by
  classical
  refine (@Fintype.card_eq_one_iff (RootedForests R) (rootedForestsFintype R)).mpr ?_
  refine ⟨⟨(fun x => False.elim ?_), ?_⟩, ?_⟩
  · exact x.2 (by simp [hR])
  · intro x
    exact ⟨0, by simp [hR]⟩
  · intro F
    apply Subtype.ext
    funext x
    exact False.elim (x.2 (by simp [hR]))

/-- The `k = n` case, stated by cardinality of the specified root set. -/
theorem card_rootedForests_all_roots_of_card {n : ℕ} (R : Finset (Fin n))
    (hcard : R.card = n) :
    @Fintype.card (RootedForests R) (rootedForestsFintype R) = 1 := by
  classical
  have hR : R = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa [Fintype.card_fin] using hcard
  exact card_rootedForests_all_roots R hR

/--
The reindexed Abel/binomial identity used by the standard depth-one recurrence
for rooted forests.  It is exactly the binomial theorem after factoring out the
initial `k`.
-/
theorem abel_forest_reindexed_identity {m k : ℕ} (hm : 0 < m) :
    (∑ i ∈ Finset.range m,
        (Nat.choose (m - 1) i) * k ^ (i + 1) * m ^ (m - 1 - i)) =
      k * (m + k) ^ (m - 1) := by
  classical
  have hmrange : (m - 1) + 1 = m := Nat.sub_add_cancel hm
  have hbinom :
      (k + m) ^ (m - 1) =
        ∑ i ∈ Finset.range m,
          (Nat.choose (m - 1) i) * k ^ i * m ^ (m - 1 - i) := by
    rw [add_pow]
    simp [hmrange, mul_assoc, mul_comm, mul_left_comm]
  calc
    (∑ i ∈ Finset.range m,
        (Nat.choose (m - 1) i) * k ^ (i + 1) * m ^ (m - 1 - i))
        =
        k * (∑ i ∈ Finset.range m,
          (Nat.choose (m - 1) i) * k ^ i * m ^ (m - 1 - i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Nat.pow_succ']
      ring_nf
    _ = k * (k + m) ^ (m - 1) := by
      rw [hbinom]
    _ = k * (m + k) ^ (m - 1) := by
      rw [Nat.add_comm]

end
end AnalyticCombinatorics.Ch2.Mappings.ForestCountNS

/-!
# Completing the rooted forest count

This file adds a carrier-polymorphic version of the rooted-forest definitions
from `ForestCount.lean`.  The immediate target is the depth-one decomposition:
for a forest whose root set is not all vertices, at least one non-root has a
root as parent.
-/

open scoped BigOperators

namespace AnalyticCombinatorics.Ch2.Mappings.ForestCountNS.Complete

noncomputable section

/-- If every vertex is a root, the empty parent map is the unique generalized forest. -/
theorem card_gRootedForests_all_roots {α : Type*} [DecidableEq α] [Fintype α]
    (R : Finset α) (hR : R = Finset.univ) :
    @Fintype.card (GRootedForests R) (gRootedForestsFintype R) = 1 := by
  classical
  refine (@Fintype.card_eq_one_iff (GRootedForests R) (gRootedForestsFintype R)).mpr ?_
  refine ⟨⟨(fun x => False.elim ?_), ?_⟩, ?_⟩
  · exact x.2 (by simp [hR])
  · intro x
    exact ⟨0, by simp [hR]⟩
  · intro F
    apply Subtype.ext
    funext x
    exact False.elim (x.2 (by simp [hR]))

/-- The boundary case with one non-root vertex, for an arbitrary finite carrier. -/
theorem card_gRootedForests_one_nonRoot {α : Type*} [DecidableEq α] [Fintype α]
    (R : Finset α) (hcard : R.card + 1 = Fintype.card α) :
    @Fintype.card (GRootedForests R) (gRootedForestsFintype R) = R.card := by
  classical
  have hnonRoot : Fintype.card (GNonRoot R) = 1 := by
    rw [card_gNonRoot R]
    omega
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp hnonRoot
  calc
    @Fintype.card (GRootedForests R) (gRootedForestsFintype R) = Fintype.card R := by
      exact @Fintype.card_congr (GRootedForests R) R (gRootedForestsFintype R) inferInstance
        (gRootedForestsEquivRootsOfUniqueNonRoot a ha)
    _ = R.card := by
      exact Fintype.card_coe R

lemma card_eq_sum_fintype_fiber {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) :
    Fintype.card A = ∑ b : B, Fintype.card {a : A // f a = b} := by
  calc
    Fintype.card A =
        Fintype.card (Sigma fun b : B => {a : A // f a = b}) := by
          exact (Fintype.card_congr (sigmaFiberEquiv f)).symm
    _ = ∑ b : B, Fintype.card {a : A // f a = b} := by
          exact Fintype.card_sigma

lemma sum_nonempty_finsets_by_card {β : Type*} [DecidableEq β] [Fintype β]
    (f : ℕ → ℕ) :
    (∑ S : {S : Finset β // S.Nonempty}, f S.1.card) =
      ∑ i ∈ Finset.range (Fintype.card β),
        Nat.choose (Fintype.card β) (i + 1) * f (i + 1) := by
  classical
  let U : Finset β := Finset.univ
  have hsub :
      (∑ S : {S : Finset β // S.Nonempty}, f S.1.card) =
        ∑ S ∈ (Finset.univ : Finset (Finset β)) with S.Nonempty, f S.card := by
    simpa using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset (Finset β)))
        (f := fun S : Finset β => f S.card)
        (p := fun S : Finset β => S.Nonempty))
  have huniv : (Finset.univ : Finset (Finset β)) = U.powerset := by
    ext S
    simp [U]
  have hinner (j : ℕ) :
      (∑ S ∈ U.powersetCard j, if S.Nonempty then f S.card else 0) =
        Nat.choose U.card j * (if j = 0 then 0 else f j) := by
    by_cases hj : j = 0
    · subst j
      simp
    · calc
        (∑ S ∈ U.powersetCard j, if S.Nonempty then f S.card else 0) =
            ∑ S ∈ U.powersetCard j, f S.card := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            have hScard : S.card = j := (Finset.mem_powersetCard.mp hS).2
            have hnon : S.Nonempty := by
              rw [← Finset.card_pos, hScard]
              omega
            simp [hnon]
        _ = Nat.choose U.card j • f j := by
            simpa using
              (Finset.sum_powersetCard (n := j) (s := U) (f := f))
        _ = Nat.choose U.card j * f j := by
            simp
        _ = Nat.choose U.card j * (if j = 0 then 0 else f j) := by
            simp [hj]
  calc
    (∑ S : {S : Finset β // S.Nonempty}, f S.1.card)
        = ∑ S ∈ U.powerset with S.Nonempty, f S.card := by
          rw [hsub, huniv]
    _ = ∑ S ∈ U.powerset, if S.Nonempty then f S.card else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ j ∈ Finset.range (U.card + 1),
          ∑ S ∈ U.powersetCard j, if S.Nonempty then f S.card else 0 := by
          rw [Finset.sum_powerset]
    _ = ∑ j ∈ Finset.range (U.card + 1),
          Nat.choose U.card j * (if j = 0 then 0 else f j) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          exact hinner j
    _ = ∑ i ∈ Finset.range U.card, Nat.choose U.card (i + 1) * f (i + 1) := by
          rw [Finset.sum_range_succ']
          simp
    _ = ∑ i ∈ Finset.range (Fintype.card β),
          Nat.choose (Fintype.card β) (i + 1) * f (i + 1) := by
          simp [U]

lemma card_fixedDepthOneData {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (S : Finset (GNonRoot R)) :
    Fintype.card (FixedDepthOneData S) =
      R.card ^ S.card *
        @Fintype.card (GRootedForests (α := GNonRoot R) S) (gRootedForestsFintype S) := by
  classical
  simp [FixedDepthOneData, Fintype.card_prod, Fintype.card_coe]

lemma card_depthOne_fiber {α : Type*} [DecidableEq α] [Fintype α]
    {R : Finset α} (hlt : R.card < Fintype.card α)
    (T : {S : Finset (GNonRoot R) // S.Nonempty}) :
    Fintype.card {F : GRootedForests R // depthOneSetSubtype hlt F = T} =
      Fintype.card (FixedDepthOneData T.1) := by
  classical
  exact Fintype.card_congr (fixedDepthOneDataEquivFiber hlt T)

lemma depthOne_card_term_eq_abel_term {m k i : ℕ} (hmpos : 0 < m) (hi : i < m) :
    Nat.choose m (i + 1) *
        (k ^ (i + 1) *
          (if i + 1 = m then 1 else (i + 1) * m ^ (m - (i + 1) - 1))) =
      Nat.choose (m - 1) i * k ^ (i + 1) * m ^ (m - 1 - i) := by
  by_cases hi_last : i + 1 = m
  · have hi_eq : i = m - 1 := by omega
    subst i
    have hif : m - 1 + 1 = m := Nat.sub_add_cancel hmpos
    simp [hif]
  · have hchoose0 := Nat.add_one_mul_choose_eq (m - 1) i
    have hsucc : (m - 1) + 1 = m := Nat.sub_add_cancel hmpos
    rw [hsucc] at hchoose0
    have hchoose : m * Nat.choose (m - 1) i = Nat.choose m (i + 1) * (i + 1) := by
      simpa [Nat.succ_eq_add_one] using hchoose0
    have hexp : m - 1 - i = (m - (i + 1) - 1) + 1 := by omega
    simp [hi_last]
    rw [hexp, Nat.pow_succ]
    calc
      Nat.choose m (i + 1) *
          (k ^ (i + 1) * ((i + 1) * m ^ (m - (i + 1) - 1)))
          = (Nat.choose m (i + 1) * (i + 1)) *
              k ^ (i + 1) * m ^ (m - (i + 1) - 1) := by
            ring
      _ = (m * Nat.choose (m - 1) i) * k ^ (i + 1) *
            m ^ (m - (i + 1) - 1) := by
            rw [← hchoose]
      _ = Nat.choose (m - 1) i * k ^ (i + 1) *
            (m ^ (m - (i + 1) - 1) * m) := by
            ring

lemma depthOne_card_sum_identity {m k : ℕ} (hmpos : 0 < m) :
    (∑ i ∈ Finset.range m,
        Nat.choose m (i + 1) *
          (k ^ (i + 1) *
            (if i + 1 = m then 1 else (i + 1) * m ^ (m - (i + 1) - 1)))) =
      k * (m + k) ^ (m - 1) := by
  calc
    (∑ i ∈ Finset.range m,
        Nat.choose m (i + 1) *
          (k ^ (i + 1) *
            (if i + 1 = m then 1 else (i + 1) * m ^ (m - (i + 1) - 1))))
        =
        ∑ i ∈ Finset.range m,
          Nat.choose (m - 1) i * k ^ (i + 1) * m ^ (m - 1 - i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact depthOne_card_term_eq_abel_term hmpos (Finset.mem_range.mp hi)
    _ = k * (m + k) ^ (m - 1) := abel_forest_reindexed_identity hmpos

theorem card_gRootedForests_aux :
    ∀ m : ℕ, ∀ {α : Type*} [DecidableEq α] [Fintype α] (R : Finset α),
      0 < R.card → Fintype.card α - R.card = m → 0 < m →
        @Fintype.card (GRootedForests R) (gRootedForestsFintype R) =
          R.card * Fintype.card α ^ (m - 1) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro α _ _ R hRpos hm hmpos
      classical
      by_cases hm1 : m = 1
      · subst m
        have hcard : R.card + 1 = Fintype.card α := by
          have hle : R.card ≤ Fintype.card α := Finset.card_le_univ R
          omega
        calc
          @Fintype.card (GRootedForests R) (gRootedForestsFintype R)
              = R.card := card_gRootedForests_one_nonRoot R hcard
          _ = R.card * Fintype.card α ^ (Fintype.card α - R.card - 1) := by
                have hexp : Fintype.card α - R.card - 1 = 0 := by omega
                simp [hexp]
      · have hlt : R.card < Fintype.card α := by
          have hle : R.card ≤ Fintype.card α := Finset.card_le_univ R
          omega
        have hnonRootCard : Fintype.card (GNonRoot R) = m := by
          rw [card_gNonRoot R, hm]
        have hpartition :
            @Fintype.card (GRootedForests R) (gRootedForestsFintype R) =
              ∑ T : {S : Finset (GNonRoot R) // S.Nonempty},
                Fintype.card (FixedDepthOneData T.1) := by
          calc
            @Fintype.card (GRootedForests R) (gRootedForestsFintype R)
                =
                ∑ T : {S : Finset (GNonRoot R) // S.Nonempty},
                  Fintype.card {F : GRootedForests R // depthOneSetSubtype hlt F = T} := by
                  exact card_eq_sum_fintype_fiber (depthOneSetSubtype hlt)
            _ = ∑ T : {S : Finset (GNonRoot R) // S.Nonempty},
                  Fintype.card (FixedDepthOneData T.1) := by
                  refine Finset.sum_congr rfl ?_
                  intro T _
                  exact card_depthOne_fiber hlt T
        let f : ℕ → ℕ :=
          fun j => R.card ^ j * (if j = m then 1 else j * m ^ (m - j - 1))
        have hfixed_eval (T : {S : Finset (GNonRoot R) // S.Nonempty}) :
            Fintype.card (FixedDepthOneData T.1) = f T.1.card := by
          have hTpos : 0 < T.1.card := T.2.card_pos
          have hTle : T.1.card ≤ m := by
            have hle : T.1.card ≤ Fintype.card (GNonRoot R) := Finset.card_le_univ T.1
            omega
          rw [card_fixedDepthOneData]
          by_cases hTm : T.1.card = m
          · have hall : T.1 = Finset.univ := by
              apply Finset.eq_univ_of_card
              simpa [hnonRootCard] using hTm
            have hinner :
                @Fintype.card (GRootedForests (α := GNonRoot R) T.1)
                    (gRootedForestsFintype T.1) = 1 :=
              card_gRootedForests_all_roots T.1 hall
            simp [f, hTm, hinner]
          · have hTlt : T.1.card < m := by omega
            have hsub_pos : 0 < m - T.1.card := by omega
            have hsub_lt : m - T.1.card < m := by omega
            have hm_inner :
                Fintype.card (GNonRoot R) - T.1.card = m - T.1.card := by
              rw [hnonRootCard]
            have hinner_raw :=
              ih (m - T.1.card) hsub_lt (α := GNonRoot R) T.1 hTpos hm_inner hsub_pos
            have hinner :
                @Fintype.card (GRootedForests (α := GNonRoot R) T.1)
                    (gRootedForestsFintype T.1) =
                  T.1.card * m ^ (m - T.1.card - 1) := by
              simpa [hnonRootCard] using hinner_raw
            simp [f, hTm, hinner]
        calc
          @Fintype.card (GRootedForests R) (gRootedForestsFintype R)
              = ∑ T : {S : Finset (GNonRoot R) // S.Nonempty},
                  Fintype.card (FixedDepthOneData T.1) := hpartition
          _ = ∑ T : {S : Finset (GNonRoot R) // S.Nonempty}, f T.1.card := by
                refine Finset.sum_congr rfl ?_
                intro T _
                exact hfixed_eval T
          _ = ∑ i ∈ Finset.range m,
                Nat.choose m (i + 1) *
                  (R.card ^ (i + 1) *
                    (if i + 1 = m then 1 else
                      (i + 1) * m ^ (m - (i + 1) - 1))) := by
                simpa [f, hnonRootCard] using
                  (sum_nonempty_finsets_by_card (β := GNonRoot R) f)
          _ = R.card * (m + R.card) ^ (m - 1) :=
                depthOne_card_sum_identity hmpos
          _ = R.card * Fintype.card α ^ (m - 1) := by
                have htotal : m + R.card = Fintype.card α := by
                  have hle : R.card ≤ Fintype.card α := Finset.card_le_univ R
                  omega
                rw [htotal]

theorem card_gRootedForests {α : Type*} [DecidableEq α] [Fintype α]
    (R : Finset α) (h0 : 0 < R.card) (hlt : R.card < Fintype.card α) :
    @Fintype.card (GRootedForests R) (gRootedForestsFintype R) =
      R.card * Fintype.card α ^ (Fintype.card α - R.card - 1) := by
  classical
  have hmpos : 0 < Fintype.card α - R.card := by omega
  exact card_gRootedForests_aux (Fintype.card α - R.card) R h0 rfl hmpos

theorem card_rootedForests {n k : ℕ} (R : Finset (Fin n)) (hk : R.card = k)
    (h0 : 0 < k) (hlt : k < n) :
    @Fintype.card (RootedForests R) (rootedForestsFintype R) =
      k * n ^ (n - k - 1) := by
  classical
  have hRpos : 0 < R.card := by omega
  have hRlt : R.card < Fintype.card (Fin n) := by
    simpa [Fintype.card_fin, hk] using hlt
  calc
    @Fintype.card (RootedForests R) (rootedForestsFintype R)
        =
        @Fintype.card (GRootedForests R) (gRootedForestsFintype R) := by
          exact @Fintype.card_congr (RootedForests R) (GRootedForests R)
            (rootedForestsFintype R) (gRootedForestsFintype R)
            (finRootedForestsEquivG R)
    _ = R.card * Fintype.card (Fin n) ^ (Fintype.card (Fin n) - R.card - 1) :=
          card_gRootedForests R hRpos hRlt
    _ = k * n ^ (n - k - 1) := by
          simp [Fintype.card_fin, hk]

end
end AnalyticCombinatorics.Ch2.Mappings.ForestCountNS.Complete

/-!
# Connected random mappings

This file banks the iteration-level periodic-core facts used in the standard
cyclic-core decomposition of connected mappings.  The exact enumeration is not
completed here.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS

noncomputable section

open AnalyticCombinatorics.Ch2.Mappings.ForestCountNS
open AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

theorem card_mapsWithFixedCore {n : ℕ} (P : Finset (Fin n)) (σ : Equiv.Perm P) :
    Fintype.card (MapsWithFixedCore P σ) =
      @Fintype.card (ForestCountNS.RootedForests P) (ForestCountNS.rootedForestsFintype P) := by
  classical
  exact @Fintype.card_congr (MapsWithFixedCore P σ) (ForestCountNS.RootedForests P)
    inferInstance (ForestCountNS.rootedForestsFintype P) (fixedCoreForestEquiv P σ)

lemma permSingleCycle_iff_isCycle_support_full_of_two_le {α : Type*}
    [DecidableEq α] [Fintype α] {σ : Equiv.Perm α}
    (hα : 2 ≤ Fintype.card α) :
    PermSingleCycle σ ↔ σ.IsCycle ∧ σ.support.card = Fintype.card α := by
  constructor
  · intro hσ
    have hmove : ∀ x : α, σ x ≠ x := by
      intro x hxfix
      rcases Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card α) x with ⟨y, hy⟩
      rcases hσ x y with ⟨m, hm⟩
      have hfixed : σ^[m] x = x := Function.iterate_fixed hxfix m
      exact hy (hm.symm.trans hfixed)
    have hsupp : σ.support = Finset.univ := by
      ext x
      simp [Equiv.Perm.mem_support, hmove x]
    refine ⟨?_, by rw [hsupp, Finset.card_univ]⟩
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card α)
    refine ⟨x, hmove x, ?_⟩
    intro y _hy
    rcases hσ x y with ⟨m, hm⟩
    refine ⟨(m : ℤ), ?_⟩
    have hpow : (σ ^ m) x = y := by
      change (⇑(σ ^ m)) x = y
      rw [Equiv.Perm.coe_pow]
      exact hm
    simpa [zpow_natCast] using hpow
  · rintro ⟨hcycle, hsupp_card⟩ x y
    have hsupp : σ.support = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa using hsupp_card
    have hx : σ x ≠ x := by
      exact Equiv.Perm.mem_support.mp (by simp [hsupp])
    have hy : σ y ≠ y := by
      exact Equiv.Perm.mem_support.mp (by simp [hsupp])
    rcases (hcycle.sameCycle hx hy).exists_nat_pow_eq with ⟨m, hm⟩
    have hiter : σ^[m] x = y := by
      change (⇑σ)^[m] x = y
      rw [← Equiv.Perm.coe_pow]
      exact hm
    exact ⟨m, hiter⟩

lemma cycleType_singleton_full_iff_permSingleCycle {α : Type*}
    [DecidableEq α] [Fintype α] {σ : Equiv.Perm α}
    (hα : 2 ≤ Fintype.card α) :
    σ.cycleType = ({Fintype.card α} : Multiset ℕ) ↔ PermSingleCycle σ := by
  constructor
  · intro htype
    have hcycle : σ.IsCycle := by
      rw [← Equiv.Perm.card_cycleType_eq_one]
      rw [htype]
      simp
    have hsupp : σ.support.card = Fintype.card α := by
      have hsum := Equiv.Perm.sum_cycleType σ
      rw [htype] at hsum
      simpa using hsum.symm
    exact (permSingleCycle_iff_isCycle_support_full_of_two_le (σ := σ) hα).mpr
      ⟨hcycle, hsupp⟩
  · intro hsingle
    rcases (permSingleCycle_iff_isCycle_support_full_of_two_le (σ := σ) hα).mp hsingle with
      ⟨hcycle, hsupp⟩
    rw [hcycle.cycleType, hsupp]

theorem card_permSingleCycle_of_two_le {α : Type*} [DecidableEq α] [Fintype α]
    (hα : 2 ≤ Fintype.card α) :
    Fintype.card {σ : Equiv.Perm α // PermSingleCycle σ} =
      (Fintype.card α - 1).factorial := by
  classical
  have hsub :
      Fintype.card {σ : Equiv.Perm α // PermSingleCycle σ} =
        ({g | g.cycleType = ({Fintype.card α} : Multiset ℕ)} :
          Finset (Equiv.Perm α)).card := by
    rw [Fintype.card_subtype]
    apply congrArg Finset.card
    ext g
    simp [cycleType_singleton_full_iff_permSingleCycle (σ := g) hα]
  rw [hsub]
  rw [Equiv.Perm.card_of_cycleType_singleton hα (le_rfl : Fintype.card α ≤ Fintype.card α)]
  simp

theorem card_permSingleCycle_of_card_le_one {α : Type*} [DecidableEq α] [Fintype α]
    (hα : Fintype.card α ≤ 1) :
    Fintype.card {σ : Equiv.Perm α // PermSingleCycle σ} = 1 := by
  classical
  have hsub : ∀ x y : α, x = y := Fintype.card_le_one_iff.mp hα
  refine Fintype.card_eq_one_iff.mpr ⟨⟨1, ?_⟩, ?_⟩
  · intro x y
    exact ⟨0, hsub x y⟩
  · intro σ
    apply Subtype.ext
    apply Equiv.Perm.ext
    intro x
    exact hsub _ _

theorem card_permSingleCycle {α : Type*} [DecidableEq α] [Fintype α] :
    Fintype.card {σ : Equiv.Perm α // PermSingleCycle σ} =
      (Fintype.card α - 1).factorial := by
  classical
  by_cases hα : 2 ≤ Fintype.card α
  · exact card_permSingleCycle_of_two_le hα
  · have hle : Fintype.card α ≤ 1 := by omega
    have hsmall : Fintype.card α = 0 ∨ Fintype.card α = 1 := by omega
    rw [card_permSingleCycle_of_card_le_one hle]
    rcases hsmall with h0 | h1
    · simp [h0]
    · simp [h1]

theorem card_connectedMapsWithFixedCore_of_single {n : ℕ} (P : Finset (Fin n))
    (σ : Equiv.Perm P) (hσ : PermSingleCycle σ) :
    @Fintype.card (ConnectedMapsWithFixedCore P σ) (connectedMapsWithFixedCoreFintype P σ) =
      @Fintype.card (ForestCountNS.RootedForests P) (ForestCountNS.rootedForestsFintype P) := by
  classical
  calc
    @Fintype.card (ConnectedMapsWithFixedCore P σ) (connectedMapsWithFixedCoreFintype P σ) =
        Fintype.card (MapsWithFixedCore P σ) := by
          exact @Fintype.card_congr (ConnectedMapsWithFixedCore P σ) (MapsWithFixedCore P σ)
            (connectedMapsWithFixedCoreFintype P σ) inferInstance
            (connectedMapsWithFixedCoreEquivOfSingle hσ)
    _ = @Fintype.card (ForestCountNS.RootedForests P)
          (ForestCountNS.rootedForestsFintype P) :=
          card_mapsWithFixedCore P σ

theorem card_connectedMapsWithFixedCore_of_not_single {n : ℕ} (P : Finset (Fin n))
    (σ : Equiv.Perm P) (hσ : ¬ PermSingleCycle σ) :
    @Fintype.card (ConnectedMapsWithFixedCore P σ) (connectedMapsWithFixedCoreFintype P σ) = 0 := by
  classical
  have hempty : IsEmpty (ConnectedMapsWithFixedCore P σ) := by
    refine ⟨fun M => ?_⟩
    exact hσ ((fixedCoreMap_connected_iff_singleCycle M.1).mp M.2)
  exact @Fintype.card_eq_zero (ConnectedMapsWithFixedCore P σ)
    (connectedMapsWithFixedCoreFintype P σ) hempty

theorem card_connectedMappings_fiber_sum {n : ℕ} (hn : 0 < n) :
    @Fintype.card (ConnectedMap n) (connectedMapFintype n) =
      ∑ P : {P : Finset (Fin n) // P.Nonempty},
        ∑ σ : Equiv.Perm P.1,
          @Fintype.card (ConnectedMapsWithFixedCore P.1 σ)
            (connectedMapsWithFixedCoreFintype P.1 σ) := by
  classical
  calc
    @Fintype.card (ConnectedMap n) (connectedMapFintype n) =
        ∑ P : {P : Finset (Fin n) // P.Nonempty},
          @Fintype.card {M : ConnectedMap n // connectedCore hn M = P}
            (Subtype.fintype (fun M : ConnectedMap n => connectedCore hn M = P)) := by
          exact @ForestCountNS.Complete.card_eq_sum_fintype_fiber
            (ConnectedMap n) {P : Finset (Fin n) // P.Nonempty}
            (connectedMapFintype n) inferInstance inferInstance (connectedCore hn)
    _ =
        ∑ P : {P : Finset (Fin n) // P.Nonempty},
          ∑ σ : Equiv.Perm P.1,
            @Fintype.card
              {M : {M : ConnectedMap n // connectedCore hn M = P} //
                connectedCoreFiberPerm P M = σ}
              (Subtype.fintype
                (fun M : {M : ConnectedMap n // connectedCore hn M = P} =>
                  connectedCoreFiberPerm P M = σ)) := by
          refine Finset.sum_congr rfl ?_
          intro P _
          exact @ForestCountNS.Complete.card_eq_sum_fintype_fiber
            {M : ConnectedMap n // connectedCore hn M = P} (Equiv.Perm P.1)
            (Subtype.fintype (fun M : ConnectedMap n => connectedCore hn M = P))
            inferInstance inferInstance (connectedCoreFiberPerm P)
    _ =
        ∑ P : {P : Finset (Fin n) // P.Nonempty},
          ∑ σ : Equiv.Perm P.1,
            @Fintype.card (ConnectedMapsWithFixedCore P.1 σ)
              (connectedMapsWithFixedCoreFintype P.1 σ) := by
          refine Finset.sum_congr rfl ?_
          intro P _
          refine Finset.sum_congr rfl ?_
          intro σ _
          exact @Fintype.card_congr
            {M : {M : ConnectedMap n // connectedCore hn M = P} //
              connectedCoreFiberPerm P M = σ}
            (ConnectedMapsWithFixedCore P.1 σ) inferInstance
            (connectedMapsWithFixedCoreFintype P.1 σ)
            (connectedCorePermFiberEquiv P σ)

theorem sum_connectedMapsWithFixedCore {n : ℕ} (P : Finset (Fin n)) :
    (∑ σ : Equiv.Perm P,
        @Fintype.card (ConnectedMapsWithFixedCore P σ)
          (connectedMapsWithFixedCoreFintype P σ)) =
      Fintype.card {σ : Equiv.Perm P // PermSingleCycle σ} *
        @Fintype.card (ForestCountNS.RootedForests P) (ForestCountNS.rootedForestsFintype P) := by
  classical
  let forestCard : ℕ :=
    @Fintype.card (ForestCountNS.RootedForests P) (ForestCountNS.rootedForestsFintype P)
  calc
    (∑ σ : Equiv.Perm P,
        @Fintype.card (ConnectedMapsWithFixedCore P σ)
          (connectedMapsWithFixedCoreFintype P σ)) =
        ∑ σ : Equiv.Perm P, if PermSingleCycle σ then forestCard else 0 := by
          refine Finset.sum_congr rfl ?_
          intro σ _
          by_cases hσ : PermSingleCycle σ
          · simp [forestCard, hσ, card_connectedMapsWithFixedCore_of_single P σ hσ]
          · simp [forestCard, hσ, card_connectedMapsWithFixedCore_of_not_single P σ hσ]
    _ =
      Fintype.card {σ : Equiv.Perm P // PermSingleCycle σ} * forestCard := by
        rw [← Finset.sum_filter]
        simp [Fintype.card_subtype]

theorem connected_fixedCore_total_by_card {n : ℕ} (P : Finset (Fin n))
    (hPpos : 0 < P.card) :
    (∑ σ : Equiv.Perm P,
        @Fintype.card (ConnectedMapsWithFixedCore P σ)
          (connectedMapsWithFixedCoreFintype P σ)) =
      (P.card - 1).factorial *
        (if P.card = n then 1 else P.card * n ^ (n - P.card - 1)) := by
  classical
  rw [sum_connectedMapsWithFixedCore P]
  rw [card_permSingleCycle]
  simp only [Fintype.card_coe]
  by_cases hcard : P.card = n
  · rw [if_pos hcard]
    rw [ForestCountNS.card_rootedForests_all_roots_of_card P hcard]
  · rw [if_neg hcard]
    have hle : P.card ≤ n := by
      simpa [Fintype.card_fin] using Finset.card_le_univ P
    have hlt : P.card < n := by omega
    rw [ForestCountNS.Complete.card_rootedForests P rfl hPpos hlt]

theorem card_connectedMappings_by_card_sum {n : ℕ} (hn : 0 < n) :
    @Fintype.card (ConnectedMap n) (connectedMapFintype n) =
      ∑ P : {P : Finset (Fin n) // P.Nonempty},
        (P.1.card - 1).factorial *
          (if P.1.card = n then 1 else P.1.card * n ^ (n - P.1.card - 1)) := by
  classical
  rw [card_connectedMappings_fiber_sum hn]
  refine Finset.sum_congr rfl ?_
  intro P _
  exact connected_fixedCore_total_by_card P.1 P.2.card_pos

theorem card_connectedMappings_range {n : ℕ} (hn : 0 < n) :
    @Fintype.card (ConnectedMap n) (connectedMapFintype n) =
      ∑ i ∈ Finset.range n,
        Nat.choose n (i + 1) *
          ((i + 1 - 1).factorial *
            (if i + 1 = n then 1 else (i + 1) * n ^ (n - (i + 1) - 1))) := by
  classical
  rw [card_connectedMappings_by_card_sum hn]
  have hsum :=
    ForestCountNS.Complete.sum_nonempty_finsets_by_card
      (β := Fin n)
      (f := fun k : ℕ =>
        (k - 1).factorial * (if k = n then 1 else k * n ^ (n - k - 1)))
  simpa [Fintype.card_fin] using hsum

lemma connected_range_term_eq_desc {n i : ℕ} (hi : i ∈ Finset.range n) :
    Nat.choose n (i + 1) *
        ((i + 1 - 1).factorial *
          (if i + 1 = n then 1 else (i + 1) * n ^ (n - (i + 1) - 1))) =
      (n - 1).descFactorial i * n ^ (n - (i + 1)) := by
  have hin : i < n := Finset.mem_range.mp hi
  by_cases hlast : i + 1 = n
  · subst n
    simp [Nat.descFactorial_self]
  · have hlt : i + 1 < n := by omega
    have hnpos : 0 < n := by omega
    have hsucc :
        n.descFactorial (i + 1) = n * (n - 1).descFactorial i := by
      have h := Nat.succ_descFactorial_succ (n - 1) i
      have hnsucc : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
      simpa [hnsucc] using h
    have hexp : n - (i + 1) = (n - (i + 1) - 1) + 1 := by omega
    rw [if_neg hlast]
    calc
      Nat.choose n (i + 1) *
          ((i + 1 - 1).factorial * ((i + 1) * n ^ (n - (i + 1) - 1))) =
          ((i + 1).factorial * Nat.choose n (i + 1)) *
            n ^ (n - (i + 1) - 1) := by
            have hsub : i + 1 - 1 = i := by omega
            rw [hsub, Nat.factorial_succ]
            ring
      _ = n.descFactorial (i + 1) * n ^ (n - (i + 1) - 1) := by
            rw [Nat.descFactorial_eq_factorial_mul_choose]
      _ = (n * (n - 1).descFactorial i) * n ^ (n - (i + 1) - 1) := by
            rw [hsucc]
      _ = (n - 1).descFactorial i * n ^ ((n - (i + 1) - 1) + 1) := by
            rw [Nat.pow_succ]
            ring
      _ = (n - 1).descFactorial i * n ^ (n - (i + 1)) := by
            rw [← hexp]

end
end AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS

open AnalyticCombinatorics AnalyticCombinatorics.Ch2 AnalyticCombinatorics.Ch2.Mappings AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS
open Filter Asymptotics
open scoped BigOperators Topology
open AnalyticCombinatorics.Ch2.Mappings.ForestCountNS
open AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS
theorem solution {n : ℕ} (hn : 0 < n) :
    Fintype.card {f : Fin n → Fin n // MappingConnected f}
      = ∑ k ∈ Finset.Icc 1 n, (n - 1).descFactorial (k - 1) * n ^ (n - k) := by
  classical
  calc
    @Fintype.card (ConnectedMap n) CategoryTheory.FinCategory.fintypeObj =
        @Fintype.card (ConnectedMap n) (connectedMapFintype n) := by
          exact @Fintype.card_congr (ConnectedMap n) (ConnectedMap n)
            CategoryTheory.FinCategory.fintypeObj (connectedMapFintype n)
            (Equiv.refl (ConnectedMap n))
    _ =
        ∑ i ∈ Finset.range n, (n - 1).descFactorial i * n ^ (n - (i + 1)) := by
          rw [card_connectedMappings_range hn]
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact connected_range_term_eq_desc hi
    _ = ∑ k ∈ Finset.Icc 1 n, (n - 1).descFactorial (k - 1) * n ^ (n - k) := by
          simpa [Finset.Ico_add_one_right_eq_Icc, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using
            (Finset.sum_Ico_eq_sum_range
              (f := fun k : ℕ => (n - 1).descFactorial (k - 1) * n ^ (n - k))
              1 (n + 1)).symm
