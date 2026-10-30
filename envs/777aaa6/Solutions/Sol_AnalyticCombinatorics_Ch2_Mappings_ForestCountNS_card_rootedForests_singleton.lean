-- Prove2me | solution 1 for AnalyticCombinatorics.Ch2.Mappings.ForestCountNS.card_rootedForests_singleton
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-25T09:49:47.55393+00:00
-- url     : https://prove2.me/submissions/0e795433-90a1-45a3-951c-8b7e5ad116f4

import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_ForestCountComplete
import Mathlib

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
# Cayley's formula (arborescence form)

The `k = 1` instantiation of the generalized forest count `card_rootedForests`:
the number of trees on `n` labeled vertices rooted at a FIXED vertex — in the functional
formulation, parent maps on the remaining `n-1` vertices under which every vertex reaches the
root — equals `n^(n-2)`.  Since unrooted labeled trees on `[n]` correspond bijectively to
arborescences toward any fixed root, this is the classical Cayley count `n^(n-2)`.

This is an honest *instantiation corollary* of `ForestCountNS.Complete.card_rootedForests`
(banked separately); it is recorded here so the textbook-named statement is explicit.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch2 AnalyticCombinatorics.Ch2.Mappings AnalyticCombinatorics.Ch2.Mappings.ForestCountNS in
theorem solution {n : ℕ} (r : Fin n) (hn : 1 < n) :
    @Fintype.card (RootedForests ({r} : Finset (Fin n)))
        (rootedForestsFintype ({r} : Finset (Fin n))) = n ^ (n - 2) := by
  have h := Complete.card_rootedForests (k := 1) ({r} : Finset (Fin n))
    (by simp) (by norm_num) (by simpa using hn)
  have hexp : n - 1 - 1 = n - 2 := by omega
  simpa [hexp] using h
