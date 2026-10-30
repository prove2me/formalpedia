-- Prove2me | solution 1 for AnalyticCombinatorics.Ch2.Mappings.CyclicPointsNS.expected_cyclicPoints_isEquivalent
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:43:52.77588+00:00
-- url     : https://prove2.me/submissions/b646cc18-364d-4164-96ea-37b3fa71d99c

import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_ForestCountComplete
import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_RamanujanQ
import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_RamanujanQSharp
import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_CyclicPoints
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
# Ramanujan's Q-function for random mappings

This file defines the finite Ramanujan Q-function from Flajolet--Sedgewick,
Chapter II.3.  The intended asymptotic is

`Q(n) ~ sqrt (pi * n / 2)`.

The full Laplace-method asymptotic is not yet present in Mathlib.  This file
records the faithful finite definition and elementary verified bounds that are
used by that proof.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

noncomputable section

lemma sum_range_succ_cast (k : ℕ) :
    (∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ))) =
      (k : ℝ) * ((k : ℝ) + 1) / 2 := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num [Nat.cast_add, Nat.cast_succ]
      ring

lemma sum_range_succ_cast_div (k n : ℕ) :
    (∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ))) =
      ((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ) := by
  rw [← Finset.sum_div, sum_range_succ_cast]

lemma ramanujanQTerm_nonneg {n k : ℕ} (hk : k ≤ n) :
    0 ≤ ramanujanQTerm n k := by
  classical
  unfold ramanujanQTerm
  refine Finset.prod_nonneg ?_
  intro j hj
  have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
  have hjn : j + 1 ≤ n := hjk.trans hk
  by_cases hn : n = 0
  · subst hn
    have : j + 1 ≤ 0 := hjn
    omega
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
  have hle : (((j + 1 : ℕ) : ℝ) / (n : ℝ)) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hnpos_nat)]
    exact_mod_cast hjn
  linarith

lemma ramanujanQTerm_factor_le_exp {n k j : ℕ} (_hk : k ≤ n) (_hj : j ∈ Finset.range k) :
    1 - (((j + 1 : ℕ) : ℝ) / (n : ℝ)) ≤
      Real.exp (-(((j + 1 : ℕ) : ℝ) / (n : ℝ))) := by
  have h := Real.add_one_le_exp (-(((j + 1 : ℕ) : ℝ) / (n : ℝ)))
  linarith

lemma ramanujanQTerm_le_exp_sum {n k : ℕ} (hk : k ≤ n) :
    ramanujanQTerm n k ≤
      Real.exp (-(∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ)))) := by
  classical
  unfold ramanujanQTerm
  calc
    (∏ j ∈ Finset.range k, (1 - (((j + 1 : ℕ) : ℝ) / (n : ℝ)))) ≤
        ∏ j ∈ Finset.range k, Real.exp (-(((j + 1 : ℕ) : ℝ) / (n : ℝ))) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro j hj
        have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
        have hjn : j + 1 ≤ n := hjk.trans hk
        by_cases hn : n = 0
        · subst hn
          have : j + 1 ≤ 0 := hjn
          omega
        have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
        have hle : (((j + 1 : ℕ) : ℝ) / (n : ℝ)) ≤ 1 := by
          rw [div_le_one (by exact_mod_cast hnpos_nat)]
          exact_mod_cast hjn
        linarith
      · intro j hj
        exact ramanujanQTerm_factor_le_exp hk hj
    _ = Real.exp (∑ j ∈ Finset.range k, -(((j + 1 : ℕ) : ℝ) / (n : ℝ))) := by
      rw [Real.exp_sum]
    _ = Real.exp (-(∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ)))) := by
      rw [Finset.sum_neg_distrib]

lemma ramanujanQTerm_le_exp_quadratic {n k : ℕ} (hk : k ≤ n) :
    ramanujanQTerm n k ≤
      Real.exp (-(((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ))) := by
  have hsum :
      (∑ j ∈ Finset.range k, (((j : ℝ) + 1) / (n : ℝ))) =
        ((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ) := by
    simpa [Nat.cast_add] using sum_range_succ_cast_div k n
  simpa [Nat.cast_add, hsum] using ramanujanQTerm_le_exp_sum (n := n) (k := k) hk

lemma gaussianKernel_antitoneOn {n : ℕ} (hn : 0 < n) (a : ℝ) :
    AntitoneOn (gaussianKernel n) (Set.Icc 0 a) := by
  intro x hx y hy hxy
  rw [gaussianKernel, gaussianKernel, Real.exp_le_exp]
  have hb_nonneg : 0 ≤ (n : ℝ)⁻¹ * 2⁻¹ := by positivity
  have hsq : x ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hx.1 hy.1).2 hxy
  have hmul : ((n : ℝ)⁻¹ * 2⁻¹) * x ^ 2 ≤
      ((n : ℝ)⁻¹ * 2⁻¹) * y ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hb_nonneg
  linarith

lemma ramanujanQTerm_le_gaussianKernel {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    ramanujanQTerm n k ≤ gaussianKernel n k := by
  have hterm := ramanujanQTerm_le_exp_quadratic (n := n) (k := k) hk
  have hquad :
      -(((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ)) ≤
        -((n : ℝ)⁻¹ * 2⁻¹ * (k : ℝ) ^ 2) := by
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
    have hsquare : (k : ℝ) ^ 2 ≤ (k : ℝ) * ((k : ℝ) + 1) := by
      nlinarith [hk_nonneg]
    have hdiv : (n : ℝ)⁻¹ * 2⁻¹ * (k : ℝ) ^ 2 ≤
        (((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ)) := by
      field_simp [hnpos.ne']
      nlinarith
    linarith
  exact hterm.trans (Real.exp_le_exp.mpr hquad)

lemma gaussianKernel_zero (n : ℕ) : gaussianKernel n 0 = 1 := by
  simp [gaussianKernel]

lemma sum_gaussianKernel_range_le_one_add_integral {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Finset.range n, gaussianKernel n k) ≤
      1 + ∫ x in (0 : ℝ)..((n - 1 : ℕ) : ℝ), gaussianKernel n x := by
  cases n with
  | zero => omega
  | succ m =>
      have hanti : AntitoneOn (gaussianKernel (m + 1)) (Set.Icc 0 (0 + (m : ℝ))) := by
        exact gaussianKernel_antitoneOn (n := m + 1) (by omega) (0 + (m : ℝ))
      have hsum := AntitoneOn.sum_le_integral (x₀ := (0 : ℝ)) (a := m) hanti
      calc
        (∑ k ∈ Finset.range (m + 1), gaussianKernel (m + 1) k) =
            (∑ k ∈ Finset.range m, gaussianKernel (m + 1) (k + 1)) + 1 := by
          rw [Finset.sum_range_succ']
          simp [gaussianKernel_zero]
        _ ≤ (∫ x in (0 : ℝ)..(0 + (m : ℝ)), gaussianKernel (m + 1) x) + 1 := by
          simpa using add_le_add_right hsum 1
        _ = 1 + ∫ x in (0 : ℝ)..((m + 1 - 1 : ℕ) : ℝ), gaussianKernel (m + 1) x := by
          simp [add_comm]

lemma integral_gaussianKernel_Ioc_le_Ioi {n : ℕ} (hn : 0 < n) :
    (∫ x in (0 : ℝ)..((n - 1 : ℕ) : ℝ), gaussianKernel n x) ≤
      ∫ x : ℝ in Set.Ioi (0 : ℝ), gaussianKernel n x := by
  have hb : 0 < 1 / (2 * (n : ℝ)) := by positivity
  have hint : MeasureTheory.IntegrableOn (gaussianKernel n) (Set.Ioi (0 : ℝ)) := by
    simpa [gaussianKernel] using
      (integrableOn_Ioi_exp_neg_mul_sq_iff (b := (n : ℝ)⁻¹ * 2⁻¹)).2 (by positivity)
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] gaussianKernel n := by
    exact Eventually.of_forall fun x => (Real.exp_pos _).le
  have hsubset : Set.Ioc (0 : ℝ) ((n - 1 : ℕ) : ℝ) ≤ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) := by
    exact Eventually.of_forall fun x hx => hx.1
  have hset :
      (∫ x in Set.Ioc (0 : ℝ) ((n - 1 : ℕ) : ℝ), gaussianKernel n x) ≤
        ∫ x : ℝ in Set.Ioi (0 : ℝ), gaussianKernel n x :=
    MeasureTheory.setIntegral_mono_set (s := Set.Ioc (0 : ℝ) ((n - 1 : ℕ) : ℝ))
      (t := Set.Ioi (0 : ℝ)) hint hnonneg hsubset
  have hle : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by positivity
  simpa [intervalIntegral.integral_of_le hle] using hset

lemma integral_gaussianKernel_Ioi {n : ℕ} (_hn : 0 < n) :
    (∫ x : ℝ in Set.Ioi (0 : ℝ), gaussianKernel n x) =
      Real.sqrt (Real.pi / ((n : ℝ)⁻¹ * 2⁻¹)) / 2 := by
  simpa [gaussianKernel] using integral_gaussian_Ioi (b := (n : ℝ)⁻¹ * 2⁻¹)

/--
One-sided sharp Gaussian-integral upper bound.  The right side is equal to
`1 + sqrt (π * n / 2)` for positive `n`.
-/
theorem ramanujanQ_le_one_add_gaussian_halfline {n : ℕ} (hn : 0 < n) :
    ramanujanQ n ≤ 1 + Real.sqrt (Real.pi / ((n : ℝ)⁻¹ * 2⁻¹)) / 2 := by
  unfold ramanujanQ
  calc
    (∑ k ∈ Finset.range n, ramanujanQTerm n k) ≤
        ∑ k ∈ Finset.range n, gaussianKernel n k := by
      refine Finset.sum_le_sum ?_
      intro k hk
      exact ramanujanQTerm_le_gaussianKernel hn (Nat.le_of_lt (Finset.mem_range.mp hk))
    _ ≤ 1 + ∫ x in (0 : ℝ)..((n - 1 : ℕ) : ℝ), gaussianKernel n x :=
      sum_gaussianKernel_range_le_one_add_integral hn
    _ ≤ 1 + ∫ x : ℝ in Set.Ioi (0 : ℝ), gaussianKernel n x := by
      exact add_le_add (le_refl 1) (integral_gaussianKernel_Ioc_le_Ioi hn)
    _ = 1 + Real.sqrt (Real.pi / ((n : ℝ)⁻¹ * 2⁻¹)) / 2 := by
      rw [integral_gaussianKernel_Ioi hn]

lemma gaussian_halfline_value_eq_sqrt_pi_mul_nat_div_two {n : ℕ} (hn : 0 < n) :
    Real.sqrt (Real.pi / ((n : ℝ)⁻¹ * 2⁻¹)) / 2 =
      Real.sqrt (Real.pi * (n : ℝ) / 2) := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have hnpos : (n : ℝ) ≠ 0 := by positivity
  field_simp [hnpos]

/-- Clean form of the one-sided Gaussian upper bound. -/
theorem ramanujanQ_le_one_add_sqrt_pi_mul_nat_div_two {n : ℕ} (hn : 0 < n) :
    ramanujanQ n ≤ 1 + Real.sqrt (Real.pi * (n : ℝ) / 2) := by
  have h := ramanujanQ_le_one_add_gaussian_halfline hn
  rw [gaussian_halfline_value_eq_sqrt_pi_mul_nat_div_two hn] at h
  exact h

end
end AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

/-!
# Sharp lower asymptotic for Ramanujan's Q-function

This file proves the missing lower comparison for Ramanujan's finite
`Q`-function and upgrades the previously banked upper bound to the sharp
equivalence `Q(n) ~ sqrt (pi * n / 2)`.
-/

open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

noncomputable section

namespace Sharp

lemma lowerCoeff_pos {m : ℕ} (hm : 0 < m) : 0 < lowerCoeff m := by
  unfold lowerCoeff
  positivity

lemma lowerCoeff_one_le {m : ℕ} (hm : 0 < m) : 1 ≤ lowerCoeff m := by
  unfold lowerCoeff
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [one_le_div hm']
  norm_num

lemma lowerGaussian_antitoneOn {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (a : ℝ) :
    AntitoneOn (lowerGaussian m n) (Set.Icc 0 a) := by
  intro x hx y hy hxy
  rw [lowerGaussian, lowerGaussian, Real.exp_le_exp]
  have hb_nonneg : 0 ≤ lowerCoeff m / (2 * (n : ℝ)) := by
    exact (div_pos (lowerCoeff_pos hm) (by positivity : (0 : ℝ) < 2 * (n : ℝ))).le
  have hsq : x ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hx.1 hy.1).2 hxy
  have hmul :
      (lowerCoeff m / (2 * (n : ℝ))) * x ^ 2 ≤
        (lowerCoeff m / (2 * (n : ℝ))) * y ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hb_nonneg
  linarith

lemma one_sub_div_pos_of_mul_le {m n i : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hi : (m + 1) * i ≤ n) :
    0 < (1 : ℝ) - (i : ℝ) / (n : ℝ) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hm1' : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hi_real : (((m + 1 : ℕ) : ℝ) * (i : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast hi
  have hle : (i : ℝ) / (n : ℝ) ≤ 1 / ((m + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hn']
    field_simp [hm1'.ne']
    linarith
  have hlt : (1 / ((m + 1 : ℕ) : ℝ) : ℝ) < 1 := by
    have hm1_gt : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_lt_succ hm
    exact (div_lt_one hm1').2 hm1_gt
  linarith

lemma log_one_sub_div_ge_scaled {m n i : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hi : (m + 1) * i ≤ n) :
    -(lowerCoeff m * ((i : ℝ) / (n : ℝ))) ≤
      Real.log (1 - (i : ℝ) / (n : ℝ)) := by
  let x : ℝ := (i : ℝ) / (n : ℝ)
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm1' : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hxlt : x < 1 := by
    simpa [x] using one_sub_div_pos_of_mul_le hm hn hi
  have hdenpos : 0 < 1 - x := by linarith
  have hi_real : (((m + 1 : ℕ) : ℝ) * (i : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast hi
  have hx_le : x ≤ 1 / ((m + 1 : ℕ) : ℝ) := by
    dsimp [x]
    rw [div_le_iff₀ hn']
    field_simp [hm1'.ne']
    linarith
  have hone_le : 1 ≤ lowerCoeff m * (1 - x) := by
    have hden_lower : (m : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ 1 - x := by
      have htmp : 1 - 1 / ((m + 1 : ℕ) : ℝ) ≤ 1 - x :=
        sub_le_sub_left hx_le 1
      have hident :
          1 - 1 / ((m + 1 : ℕ) : ℝ) =
            (m : ℝ) / ((m + 1 : ℕ) : ℝ) := by
        field_simp [hm1'.ne']
        norm_num
      rwa [← hident]
    calc
      1 = lowerCoeff m * ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
        unfold lowerCoeff
        field_simp [hm'.ne', hm1'.ne']
      _ ≤ lowerCoeff m * (1 - x) :=
        mul_le_mul_of_nonneg_left hden_lower (lowerCoeff_pos hm).le
  have hfrac_le : x / (1 - x) ≤ lowerCoeff m * x := by
    rw [div_le_iff₀ hdenpos]
    calc
      x ≤ x * (lowerCoeff m * (1 - x)) := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hone_le hx_nonneg
      _ = lowerCoeff m * x * (1 - x) := by ring
  have hbase : 1 - (1 - x)⁻¹ = -x / (1 - x) := by
    field_simp [hdenpos.ne']
    ring
  have hlog := Real.one_sub_inv_le_log_of_pos hdenpos
  rw [hbase] at hlog
  change -(lowerCoeff m * x) ≤ Real.log (1 - x)
  have hneg : -(lowerCoeff m * x) ≤ -x / (1 - x) := by
    simpa [neg_div] using neg_le_neg hfrac_le
  exact hneg.trans hlog

lemma ramanujanQTerm_ge_exp_lowerCoeff {m n k : ℕ} (hm : 0 < m)
    (hk : k < n / (m + 1)) :
    Real.exp (-((lowerCoeff m / (2 * (n : ℝ))) *
        ((k : ℝ) * ((k : ℝ) + 1)))) ≤ ramanujanQTerm n k := by
  classical
  have hqpos : 0 < n / (m + 1) :=
    lt_of_le_of_lt (Nat.zero_le k) hk
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    simp [hn0] at hqpos
  let f : ℕ → ℝ := fun j => 1 - (((j + 1 : ℕ) : ℝ) / (n : ℝ))
  have hfactor_pos : ∀ j ∈ Finset.range k, 0 < f j := by
    intro j hj
    have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
    have hle_div : j + 1 ≤ n / (m + 1) := le_trans hjk (le_of_lt hk)
    have hmul₁ : (m + 1) * (j + 1) ≤ (m + 1) * (n / (m + 1)) :=
      Nat.mul_le_mul_left (m + 1) hle_div
    have hmul₂ : (m + 1) * (n / (m + 1)) ≤ n := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self n (m + 1)
    exact one_sub_div_pos_of_mul_le hm hn (le_trans hmul₁ hmul₂)
  have hsumlog :
      -lowerCoeff m *
          (∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ))) ≤
        ∑ j ∈ Finset.range k, Real.log (f j) := by
    calc
      -lowerCoeff m *
          (∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ))) =
          ∑ j ∈ Finset.range k,
            (-(lowerCoeff m * (((j + 1 : ℕ) : ℝ) / (n : ℝ)))) := by
        simp [Finset.mul_sum, mul_comm]
      _ ≤ ∑ j ∈ Finset.range k, Real.log (f j) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
        have hle_div : j + 1 ≤ n / (m + 1) := le_trans hjk (le_of_lt hk)
        have hmul₁ : (m + 1) * (j + 1) ≤ (m + 1) * (n / (m + 1)) :=
          Nat.mul_le_mul_left (m + 1) hle_div
        have hmul₂ : (m + 1) * (n / (m + 1)) ≤ n := by
          simpa [Nat.mul_comm] using Nat.div_mul_le_self n (m + 1)
        simpa [f] using
          log_one_sub_div_ge_scaled hm hn (i := j + 1) (le_trans hmul₁ hmul₂)
  have hsum_eval :
      (∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ))) =
        (((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ)) := by
    simpa [Nat.cast_add] using sum_range_succ_cast_div k n
  have hprod_pos : 0 < ∏ j ∈ Finset.range k, f j := by
    exact Finset.prod_pos hfactor_pos
  have hlogprod :
      Real.log (∏ j ∈ Finset.range k, f j) =
        ∑ j ∈ Finset.range k, Real.log (f j) := by
    exact Real.log_prod fun j hj => (hfactor_pos j hj).ne'
  calc
    Real.exp (-((lowerCoeff m / (2 * (n : ℝ))) *
        ((k : ℝ) * ((k : ℝ) + 1)))) =
        Real.exp (-lowerCoeff m *
          (∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ)))) := by
      rw [hsum_eval]
      have hn' : (n : ℝ) ≠ 0 := by positivity
      field_simp [hn']
    _ ≤ Real.exp (∑ j ∈ Finset.range k, Real.log (f j)) :=
      Real.exp_le_exp.mpr hsumlog
    _ = ∏ j ∈ Finset.range k, f j := by
      rw [← hlogprod, Real.exp_log hprod_pos]
    _ = ramanujanQTerm n k := by
      simp [ramanujanQTerm, f]

lemma lowerGaussian_succ_le_ramanujanQTerm {m n k : ℕ} (hm : 0 < m)
    (hk : k < n / (m + 1)) :
    lowerGaussian m n (k + 1 : ℕ) ≤ ramanujanQTerm n k := by
  have hqpos : 0 < n / (m + 1) :=
    lt_of_le_of_lt (Nat.zero_le k) hk
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    simp [hn0] at hqpos
  have hb_nonneg : 0 ≤ lowerCoeff m / (2 * (n : ℝ)) := by
    exact (div_pos (lowerCoeff_pos hm) (by positivity : (0 : ℝ) < 2 * (n : ℝ))).le
  have hsq :
      (k : ℝ) * ((k : ℝ) + 1) ≤ ((k : ℝ) + 1) ^ 2 := by
    nlinarith
  have hexp :
      lowerGaussian m n (k + 1 : ℕ) ≤
        Real.exp (-((lowerCoeff m / (2 * (n : ℝ))) *
          ((k : ℝ) * ((k : ℝ) + 1)))) := by
    rw [lowerGaussian, Real.exp_le_exp]
    have hmul :
        (lowerCoeff m / (2 * (n : ℝ))) * ((k : ℝ) * ((k : ℝ) + 1)) ≤
          (lowerCoeff m / (2 * (n : ℝ))) * (((k : ℝ) + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq hb_nonneg
    have hcast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by norm_num
    rw [hcast]
    linarith
  exact hexp.trans (ramanujanQTerm_ge_exp_lowerCoeff hm hk)

lemma lowerGaussian_integrableOn_Ioi {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (c : ℝ) :
    IntegrableOn (lowerGaussian m n) (Set.Ioi c) := by
  have hb : 0 < lowerCoeff m / (2 * (n : ℝ)) := by
    exact div_pos (lowerCoeff_pos hm) (by positivity : (0 : ℝ) < 2 * (n : ℝ))
  simpa [lowerGaussian] using
    (integrable_exp_neg_mul_sq hb).integrableOn (s := Set.Ioi c)

lemma lowerGaussian_integral_Ioi {m n : ℕ} (_hm : 0 < m) (_hn : 0 < n) :
    (∫ x : ℝ in Set.Ioi (0 : ℝ), lowerGaussian m n x) =
      Real.sqrt (Real.pi / (lowerCoeff m / (2 * (n : ℝ)))) / 2 := by
  simpa [lowerGaussian] using
    integral_gaussian_Ioi (b := lowerCoeff m / (2 * (n : ℝ)))

lemma lowerGaussian_halfline_value {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Real.sqrt (Real.pi / (lowerCoeff m / (2 * (n : ℝ)))) / 2 =
      Real.sqrt (Real.pi * (n : ℝ) / 2) *
        Real.sqrt ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
  apply (sq_eq_sq₀ (by positivity) (by
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  have hleft_nonneg : 0 ≤ Real.pi / (lowerCoeff m / (2 * (n : ℝ))) := by
    have hb : 0 < lowerCoeff m / (2 * (n : ℝ)) :=
      div_pos (lowerCoeff_pos hm) (by positivity : (0 : ℝ) < 2 * (n : ℝ))
    exact div_nonneg Real.pi_pos.le hb.le
  have hright₁ : 0 ≤ Real.pi * (n : ℝ) / 2 := by positivity
  have hright₂ : 0 ≤ (m : ℝ) / ((m + 1 : ℕ) : ℝ) := by positivity
  rw [div_pow, mul_pow, Real.sq_sqrt hleft_nonneg, Real.sq_sqrt hright₁,
    Real.sq_sqrt hright₂]
  unfold lowerCoeff
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hm1' : (((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hm', hn', hm1']

lemma lowerGaussian_integral_zero_one_le_one {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..(1 : ℝ), lowerGaussian m n x) ≤ 1 := by
  have hle : ∀ x ∈ Set.Icc (0 : ℝ) 1, lowerGaussian m n x ≤ (1 : ℝ) := by
    intro x hx
    rw [lowerGaussian, ← Real.exp_zero, Real.exp_le_exp]
    have hb_nonneg : 0 ≤ lowerCoeff m / (2 * (n : ℝ)) := by
      exact (div_pos (lowerCoeff_pos hm) (by positivity : (0 : ℝ) < 2 * (n : ℝ))).le
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    nlinarith [mul_nonneg hb_nonneg hx2]
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    ((by unfold lowerGaussian; fun_prop : Continuous (lowerGaussian m n)).intervalIntegrable 0 1)
    (intervalIntegral.intervalIntegrable_const (a := (0 : ℝ)) (b := 1) (c := (1 : ℝ)))
    hle
  simpa using hmono

lemma lowerGaussian_tail_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {K : ℝ}
    (hK : 0 < K) :
    (∫ x : ℝ in Set.Ioi K, lowerGaussian m n x) ≤
      1 / ((lowerCoeff m / (2 * (n : ℝ))) * K) := by
  let b : ℝ := lowerCoeff m / (2 * (n : ℝ))
  have hb : 0 < b := by
    dsimp [b]
    exact div_pos (lowerCoeff_pos hm) (by positivity : (0 : ℝ) < 2 * (n : ℝ))
  have hbK : 0 < b * K := mul_pos hb hK
  have hgauss_int : IntegrableOn (lowerGaussian m n) (Set.Ioi K) :=
    lowerGaussian_integrableOn_Ioi hm hn K
  have hlin_int : IntegrableOn (fun x : ℝ => Real.exp (-(b * K) * x)) (Set.Ioi K) := by
    exact integrableOn_exp_mul_Ioi (a := -(b * K)) (by linarith) K
  have hmono :
      (∫ x : ℝ in Set.Ioi K, lowerGaussian m n x) ≤
        ∫ x : ℝ in Set.Ioi K, Real.exp (-(b * K) * x) := by
    refine setIntegral_mono_on hgauss_int hlin_int measurableSet_Ioi ?_
    intro x hx
    have hxK : K ≤ x := le_of_lt hx
    have hx_nonneg : 0 ≤ x := le_trans hK.le hxK
    rw [lowerGaussian, Real.exp_le_exp]
    dsimp [b]
    have hsq : K * x ≤ x ^ 2 := by
      nlinarith
    have hmul : b * (K * x) ≤ b * x ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hb.le
    nlinarith
  calc
    (∫ x : ℝ in Set.Ioi K, lowerGaussian m n x) ≤
        ∫ x : ℝ in Set.Ioi K, Real.exp (-(b * K) * x) := hmono
    _ = Real.exp (-(b * K) * K) / (b * K) := by
      have h := integral_exp_mul_Ioi (a := -(b * K)) (by linarith : -(b * K) < 0) K
      rw [h]
      field_simp [hbK.ne']
    _ ≤ 1 / (b * K) := by
      have hexp : Real.exp (-(b * K) * K) ≤ 1 := by
        rw [← Real.exp_zero, Real.exp_le_exp]
        nlinarith
      exact div_le_div_of_nonneg_right hexp hbK.le

lemma lowerGaussian_tail_le_linear_head {m n : ℕ} (hm : 0 < m) (hn : m + 1 ≤ n) :
    (∫ x : ℝ in Set.Ioi (1 + (((n / (m + 1) : ℕ) : ℝ))), lowerGaussian m n x) ≤
      2 * ((m + 1 : ℕ) : ℝ) := by
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.succ_pos m) hn
  let K : ℝ := 1 + ((n / (m + 1) : ℕ) : ℝ)
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  have htail := lowerGaussian_tail_le hm hnpos (K := K) hKpos
  have hdivlt_nat : n < (n / (m + 1) + 1) * (m + 1) := by
    have hlt : n / (m + 1) < n / (m + 1) + 1 := Nat.lt_succ_self _
    exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos m)).mp hlt
  have hdivle_real : (n : ℝ) / K ≤ ((m + 1 : ℕ) : ℝ) := by
    have hlt_real :
        (n : ℝ) < (((n / (m + 1) + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
      exact_mod_cast hdivlt_nat
    have hK_eq : K = ((n / (m + 1) + 1 : ℕ) : ℝ) := by
      dsimp [K]
      rw [Nat.cast_add, Nat.cast_one]
      ring
    rw [hK_eq]
    have hKpos' : 0 < (((n / (m + 1) + 1 : ℕ) : ℝ)) := by positivity
    rw [div_le_iff₀ hKpos']
    exact le_of_lt (by simpa [mul_comm] using hlt_real)
  have hcoeff_ge : 1 ≤ lowerCoeff m := lowerCoeff_one_le hm
  have hmain :
      1 / ((lowerCoeff m / (2 * (n : ℝ))) * K) ≤
        2 * ((m + 1 : ℕ) : ℝ) := by
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hKreal : 0 < K := hKpos
    have hcoeff_pos : 0 < lowerCoeff m := lowerCoeff_pos hm
    calc
      1 / ((lowerCoeff m / (2 * (n : ℝ))) * K)
          = (2 * (n : ℝ)) / (lowerCoeff m * K) := by
        field_simp [hnreal.ne', hKreal.ne', hcoeff_pos.ne']
      _ ≤ (2 * (n : ℝ)) / K := by
        have hden_le : K ≤ lowerCoeff m * K := by
          simpa using mul_le_mul_of_nonneg_right hcoeff_ge hKreal.le
        exact div_le_div_of_nonneg_left (by positivity) hKreal hden_le
      _ = 2 * ((n : ℝ) / K) := by ring
      _ ≤ 2 * ((m + 1 : ℕ) : ℝ) := by
        nlinarith
  exact htail.trans hmain

theorem ramanujanQ_lower_fixed (m n : ℕ) (hm : 0 < m) (hn : m + 1 ≤ n) :
    Real.sqrt (Real.pi * (n : ℝ) / 2) *
        Real.sqrt ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) -
        (1 + 2 * ((m + 1 : ℕ) : ℝ)) ≤ ramanujanQ n := by
  classical
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.succ_pos m) hn
  let K : ℕ := n / (m + 1)
  have hK_le_n : K ≤ n := Nat.div_le_self n (m + 1)
  have hsubset : Finset.range K ⊆ Finset.range n := by
    intro k hk
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hK_le_n)
  have hQ_head :
      (∑ k ∈ Finset.range K, ramanujanQTerm n k) ≤ ramanujanQ n := by
    unfold ramanujanQ
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro k hk _hnot
    exact ramanujanQTerm_nonneg (Nat.le_of_lt (Finset.mem_range.mp hk))
  have hterm :
      (∑ k ∈ Finset.range K, lowerGaussian m n (k + 1 : ℕ)) ≤
        ∑ k ∈ Finset.range K, ramanujanQTerm n k := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact lowerGaussian_succ_le_ramanujanQTerm hm (Finset.mem_range.mp hk)
  have hanti :
      AntitoneOn (lowerGaussian m n)
        (Set.Icc (1 : ℝ) (1 + (K : ℝ))) := by
    exact (lowerGaussian_antitoneOn hm hnpos (1 + (K : ℝ))).mono
      (by
        intro x hx
        exact ⟨by linarith [hx.1], hx.2⟩)
  have hint_le_sum :
      (∫ x in (1 : ℝ)..(1 + (K : ℝ)), lowerGaussian m n x) ≤
        ∑ k ∈ Finset.range K, lowerGaussian m n (1 + k) :=
    AntitoneOn.integral_le_sum hanti
  have hsum_cast :
      (∑ k ∈ Finset.range K, lowerGaussian m n (1 + k)) =
        ∑ k ∈ Finset.range K, lowerGaussian m n (k + 1 : ℕ) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    congr 1
    simp [Nat.cast_add, add_comm]
  have hintegral_head :
      (∫ x in (1 : ℝ)..(1 + (K : ℝ)), lowerGaussian m n x) ≤ ramanujanQ n := by
    calc
      (∫ x in (1 : ℝ)..(1 + (K : ℝ)), lowerGaussian m n x) ≤
          ∑ k ∈ Finset.range K, lowerGaussian m n (1 + k) := hint_le_sum
      _ = ∑ k ∈ Finset.range K, lowerGaussian m n (k + 1 : ℕ) := hsum_cast
      _ ≤ ∑ k ∈ Finset.range K, ramanujanQTerm n k := hterm
      _ ≤ ramanujanQ n := hQ_head
  have htail := lowerGaussian_tail_le_linear_head hm hn
  have h01 := lowerGaussian_integral_zero_one_le_one hm hnpos
  have hint0 := lowerGaussian_integrableOn_Ioi hm hnpos (0 : ℝ)
  have hint1 := lowerGaussian_integrableOn_Ioi hm hnpos (1 : ℝ)
  have hintK := lowerGaussian_integrableOn_Ioi hm hnpos (1 + (K : ℝ))
  have h01eq :
      (∫ x : ℝ in Set.Ioi (0 : ℝ), lowerGaussian m n x) -
        (∫ x : ℝ in Set.Ioi (1 : ℝ), lowerGaussian m n x) =
          ∫ x in (0 : ℝ)..(1 : ℝ), lowerGaussian m n x :=
    (eq_sub_of_add_eq (intervalIntegral.integral_interval_add_Ioi hint0 hint1)).symm
  have h1Keq :
      (∫ x : ℝ in Set.Ioi (1 : ℝ), lowerGaussian m n x) -
        (∫ x : ℝ in Set.Ioi (1 + (K : ℝ)), lowerGaussian m n x) =
          ∫ x in (1 : ℝ)..(1 + (K : ℝ)), lowerGaussian m n x :=
    (eq_sub_of_add_eq (intervalIntegral.integral_interval_add_Ioi hint1 hintK)).symm
  have hhalf :
      (∫ x : ℝ in Set.Ioi (0 : ℝ), lowerGaussian m n x) =
        Real.sqrt (Real.pi * (n : ℝ) / 2) *
          Real.sqrt ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
    rw [lowerGaussian_integral_Ioi hm hnpos, lowerGaussian_halfline_value hm hnpos]
  have hdecomp :
      Real.sqrt (Real.pi * (n : ℝ) / 2) *
          Real.sqrt ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) -
          (1 + 2 * ((m + 1 : ℕ) : ℝ)) ≤
        ∫ x in (1 : ℝ)..(1 + (K : ℝ)), lowerGaussian m n x := by
    rw [← hhalf]
    linarith
  exact hdecomp.trans hintegral_head

lemma tendsto_sqrt_nat_div_nat_succ :
    Tendsto (fun m : ℕ => Real.sqrt ((m : ℝ) / ((m + 1 : ℕ) : ℝ))) atTop (𝓝 1) := by
  have h := (tendsto_natCast_div_add_atTop (1 : ℝ)).sqrt
  simpa [Nat.cast_add, Real.sqrt_one] using h

lemma tendsto_sqrt_pi_mul_nat_div_two_atTop :
    Tendsto (fun n : ℕ => Real.sqrt (Real.pi * (n : ℝ) / 2)) atTop atTop := by
  have hlin :
      Tendsto (fun n : ℕ => (Real.pi / 2) * (n : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) tendsto_natCast_atTop_atTop
  refine Real.tendsto_sqrt_atTop.comp (hlin.congr' ?_)
  exact Eventually.of_forall fun n => by ring

lemma eventually_ratio_le_of_gt_one {a : ℝ} (ha : 1 < a) :
    ∀ᶠ n : ℕ in atTop,
      ramanujanQ n / Real.sqrt (Real.pi * (n : ℝ) / 2) < a := by
  let g : ℕ → ℝ := fun n => Real.sqrt (Real.pi * (n : ℝ) / 2)
  have hg : Tendsto g atTop atTop := tendsto_sqrt_pi_mul_nat_div_two_atTop
  have hsmall :
      ∀ᶠ n : ℕ in atTop, (1 : ℝ) / g n < a - 1 :=
    (Filter.Tendsto.const_div_atTop hg (1 : ℝ)).eventually
      (gt_mem_nhds (sub_pos.mpr ha))
  filter_upwards [hsmall, eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hsmall hn
  have hnpos : 0 < n := by omega
  have gpos : 0 < g n := by
    dsimp [g]
    positivity
  have hQ := ramanujanQ_le_one_add_sqrt_pi_mul_nat_div_two hnpos
  have hratio :
      ramanujanQ n / g n ≤ 1 + 1 / g n := by
    calc
      ramanujanQ n / g n ≤ (1 + g n) / g n :=
        div_le_div_of_nonneg_right hQ gpos.le
      _ = 1 + 1 / g n := by
        field_simp [gpos.ne']
        ring
  linarith

lemma eventually_ratio_gt_of_lt_one {a : ℝ} (ha : a < 1) :
    ∀ᶠ n : ℕ in atTop,
      a < ramanujanQ n / Real.sqrt (Real.pi * (n : ℝ) / 2) := by
  let s : ℕ → ℝ := fun m => Real.sqrt ((m : ℝ) / ((m + 1 : ℕ) : ℝ))
  have hs_tendsto : Tendsto s atTop (𝓝 1) := tendsto_sqrt_nat_div_nat_succ
  have hs_event : ∀ᶠ m : ℕ in atTop, a < s m :=
    (tendsto_order.mp hs_tendsto).1 a ha
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp hs_event
  let m : ℕ := max 1 m₀
  have hm : 0 < m := by
    dsimp [m]
    omega
  have hma : a < s m := hm₀ m (by
    dsimp [m]
    exact le_max_right 1 m₀)
  let g : ℕ → ℝ := fun n => Real.sqrt (Real.pi * (n : ℝ) / 2)
  have hg : Tendsto g atTop atTop := tendsto_sqrt_pi_mul_nat_div_two_atTop
  let C : ℝ := 1 + 2 * ((m + 1 : ℕ) : ℝ)
  have hgap : 0 < s m - a := sub_pos.mpr hma
  have hsmall :
      ∀ᶠ n : ℕ in atTop, C / g n < s m - a :=
    (Filter.Tendsto.const_div_atTop hg C).eventually (gt_mem_nhds hgap)
  filter_upwards [hsmall, eventually_atTop.2 ⟨m + 1, fun n hn => hn⟩] with n hsmall hn
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.succ_pos m) hn
  have gpos : 0 < g n := by
    dsimp [g]
    positivity
  have hlower := ramanujanQ_lower_fixed m n hm hn
  have hratio_lower :
      s m - C / g n ≤ ramanujanQ n / g n := by
    calc
      s m - C / g n =
          (g n * s m - C) / g n := by
        field_simp [gpos.ne']
      _ ≤ ramanujanQ n / g n :=
        div_le_div_of_nonneg_right hlower gpos.le
  linarith

theorem ramanujanQ_tendsto_ratio_one :
    Tendsto
      (fun n : ℕ => ramanujanQ n / Real.sqrt (Real.pi * (n : ℝ) / 2))
      atTop (𝓝 1) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact eventually_ratio_gt_of_lt_one ha
  · intro a ha
    exact eventually_ratio_le_of_gt_one ha

theorem ramanujanQ_isEquivalent :
    (fun n : ℕ => ramanujanQ n) ~[atTop]
      (fun n : ℕ => Real.sqrt (Real.pi * (n : ℝ) / 2)) := by
  exact Asymptotics.isEquivalent_of_tendsto_one ramanujanQ_tendsto_ratio_one

end Sharp
end
end AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

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

theorem card_connectedMappings {n : ℕ} (hn : 0 < n) :
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

lemma ramanujanQTerm_eq_descFactorial_div {n k : ℕ} (hn : 0 < n) (hk : k < n) :
    RamanujanQNS.ramanujanQTerm n k =
      ((n - 1).descFactorial k : ℝ) / (n : ℝ) ^ k := by
  classical
  have hnne : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  let qFactor : ℕ → ℝ :=
    fun j : ℕ => (1 : ℝ) - (((j + 1 : ℕ) : ℝ) / (n : ℝ))
  let dFactor : ℕ → ℝ :=
    fun j : ℕ => ((n - 1 - j : ℕ) : ℝ) / (n : ℝ)
  have hfactor (j : ℕ) (hj : j ∈ Finset.range k) :
      qFactor j = dFactor j := by
    have hjk : j < k := Finset.mem_range.mp hj
    have hle : j + 1 ≤ n := by omega
    have hsub : n - (j + 1) = n - 1 - j := by omega
    dsimp [qFactor, dFactor]
    rw [← hsub]
    rw [Nat.cast_sub hle]
    field_simp [hnne]
  unfold RamanujanQNS.ramanujanQTerm
  change (∏ j ∈ Finset.range k, qFactor j) =
    ((n - 1).descFactorial k : ℝ) / (n : ℝ) ^ k
  calc
    (∏ j ∈ Finset.range k, qFactor j) =
        ∏ j ∈ Finset.range k, dFactor j := by
          refine Finset.prod_congr rfl ?_
          intro j hj
          exact hfactor j hj
    _ =
        ∏ j ∈ Finset.range k, (((n - 1 - j : ℕ) : ℝ) / (n : ℝ)) := by
          rfl
    _ =
        (∏ j ∈ Finset.range k, ((n - 1 - j : ℕ) : ℝ)) /
          ∏ _j ∈ Finset.range k, (n : ℝ) := by
          rw [Finset.prod_div_distrib]
    _ =
        ((∏ j ∈ Finset.range k, (n - 1 - j : ℕ)) : ℝ) / (n : ℝ) ^ k := by
          rw [Finset.prod_const]
          simp only [Finset.card_range]
    _ = ((n - 1).descFactorial k : ℝ) / (n : ℝ) ^ k := by
          rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]

lemma ramanujanQTerm_scaled_eq_desc {n k : ℕ} (hn : 0 < n) (hk : k < n) :
    (n : ℝ) ^ (n - 1) * RamanujanQNS.ramanujanQTerm n k =
      ((n - 1).descFactorial k * n ^ (n - (k + 1)) : ℕ) := by
  have hnne : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  have hpow_ne : (n : ℝ) ^ k ≠ 0 := pow_ne_zero k hnne
  have hsplit : n - 1 = k + (n - 1 - k) := by omega
  have hexp : n - 1 - k = n - (k + 1) := by omega
  have hpow_split :
      (n : ℝ) ^ (n - 1) = (n : ℝ) ^ k * (n : ℝ) ^ (n - 1 - k) := by
    rw [hsplit, pow_add]
    have htail : k + (n - 1 - k) - k = n - 1 - k := by omega
    rw [htail]
  rw [ramanujanQTerm_eq_descFactorial_div hn hk]
  calc
    (n : ℝ) ^ (n - 1) *
        (((n - 1).descFactorial k : ℝ) / (n : ℝ) ^ k) =
        ((n : ℝ) ^ k * (n : ℝ) ^ (n - 1 - k)) *
          (((n - 1).descFactorial k : ℝ) / (n : ℝ) ^ k) := by
          rw [hpow_split]
    _ = ((n - 1).descFactorial k : ℝ) * (n : ℝ) ^ (n - 1 - k) := by
          field_simp [hpow_ne]
    _ = ((n - 1).descFactorial k * n ^ (n - (k + 1)) : ℕ) := by
          rw [hexp]
          simp

theorem card_connectedMappings_eq_q {n : ℕ} (hn : 0 < n) :
    (Fintype.card {f : Fin n → Fin n // MappingConnected f} : ℝ) =
      (n : ℝ) ^ (n - 1) * RamanujanQNS.ramanujanQ n := by
  classical
  rw [card_connectedMappings hn]
  have hreindex :
      (∑ k ∈ Finset.Icc 1 n, (n - 1).descFactorial (k - 1) * n ^ (n - k)) =
        ∑ i ∈ Finset.range n, (n - 1).descFactorial i * n ^ (n - (i + 1)) := by
    simpa [Finset.Ico_add_one_right_eq_Icc, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using
      (Finset.sum_Ico_eq_sum_range
        (f := fun k : ℕ => (n - 1).descFactorial (k - 1) * n ^ (n - k))
        1 (n + 1))
  rw [hreindex]
  rw [Nat.cast_sum]
  rw [RamanujanQNS.ramanujanQ, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  exact (ramanujanQTerm_scaled_eq_desc hn (Finset.mem_range.mp hk)).symm

end
end AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS

/-!
# Cyclic points in random mappings

This file counts mappings for which a fixed point is cyclic and derives the
expected number of cyclic points from Ramanujan's finite `Q`-function.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.CyclicPointsNS

noncomputable section

open AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS

theorem card_firstReturnFiber_length {n l : ℕ} (x₀ : Fin n) :
    Fintype.card
      {f : Fin n → Fin n //
        f^[l + 1] x₀ = x₀ ∧
          ∀ m : ℕ, 0 < m → m < l + 1 → f^[m] x₀ ≠ x₀} =
      Fintype.card (CycleFiberData x₀ l) := by
  classical
  let P : (Fin n → Fin n) → Prop :=
    fun f => f^[l + 1] x₀ = x₀ ∧
      ∀ m : ℕ, 0 < m → m < l + 1 → f^[m] x₀ ≠ x₀
  change @Fintype.card {f : Fin n → Fin n // P f} CategoryTheory.FinCategory.fintypeObj =
    Fintype.card (CycleFiberData x₀ l)
  calc
    @Fintype.card {f : Fin n → Fin n // P f} CategoryTheory.FinCategory.fintypeObj =
        @Fintype.card {f : Fin n → Fin n // P f} (Subtype.fintype P) := by
          exact @Fintype.card_congr {f : Fin n → Fin n // P f} {f : Fin n → Fin n // P f}
            CategoryTheory.FinCategory.fintypeObj (Subtype.fintype P) (Equiv.refl _)
    _ = Fintype.card (CycleFiberData x₀ l) := by
          exact (Fintype.card_congr (cycleFiberFirstReturnEquiv (n := n) (l := l) x₀)).symm

lemma card_tailEmbedding {n l : ℕ} (x₀ : Fin n) :
    Fintype.card (TailEmbedding x₀ l) = (n - 1).descFactorial l := by
  classical
  simp [TailEmbedding, card_nonBase x₀]

lemma card_freeDomain {n l : ℕ} {x₀ : Fin n} (e : TailEmbedding x₀ l) :
    Fintype.card (FreeDomain e) = n - 1 - l := by
  classical
  change Fintype.card {x : NonBase x₀ // ¬ x ∈ Set.range e} = n - 1 - l
  rw [Fintype.card_subtype_compl (fun x : NonBase x₀ => x ∈ Set.range e)]
  rw [Fintype.card_range e, Fintype.card_fin, card_nonBase x₀]

lemma card_freeDomain_of_mem_Icc {n k : ℕ} {x₀ : Fin n}
    (hk : k ∈ Finset.Icc 1 n) (e : TailEmbedding x₀ (k - 1)) :
    Fintype.card (FreeDomain e) = n - k := by
  classical
  have hbase := card_freeDomain e
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  omega

lemma card_cycleFiberData_of_mem_Icc {n k : ℕ} (x₀ : Fin n)
    (hk : k ∈ Finset.Icc 1 n) :
    Fintype.card (CycleFiberData x₀ (k - 1)) =
      (n - 1).descFactorial (k - 1) * n ^ (n - k) := by
  classical
  change Fintype.card (Sigma fun e : TailEmbedding x₀ (k - 1) => FreeDomain e → Fin n) =
      (n - 1).descFactorial (k - 1) * n ^ (n - k)
  rw [Fintype.card_sigma]
  calc
    (∑ e : TailEmbedding x₀ (k - 1), Fintype.card (FreeDomain e → Fin n)) =
        ∑ e : TailEmbedding x₀ (k - 1), n ^ (n - k) := by
          refine Finset.sum_congr rfl ?_
          intro e _
          rw [Fintype.card_fun]
          rw [Fintype.card_fin, card_freeDomain_of_mem_Icc hk e]
    _ = Fintype.card (TailEmbedding x₀ (k - 1)) * n ^ (n - k) := by
          simp
    _ = (n - 1).descFactorial (k - 1) * n ^ (n - k) := by
          rw [card_tailEmbedding x₀]

theorem card_firstReturnFiber {n k : ℕ} (x₀ : Fin n)
    (hk : k ∈ Finset.Icc 1 n) :
    Fintype.card
      {f : Fin n → Fin n //
        f^[k] x₀ = x₀ ∧
          ∀ m : ℕ, 0 < m → m < k → f^[m] x₀ ≠ x₀} =
      (n - 1).descFactorial (k - 1) * n ^ (n - k) := by
  classical
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hsucc : k - 1 + 1 = k := Nat.sub_add_cancel hk1
  let P : (Fin n → Fin n) → Prop :=
    fun f => f^[k] x₀ = x₀ ∧
      ∀ m : ℕ, 0 < m → m < k → f^[m] x₀ ≠ x₀
  change @Fintype.card {f : Fin n → Fin n // P f} CategoryTheory.FinCategory.fintypeObj =
    (n - 1).descFactorial (k - 1) * n ^ (n - k)
  calc
    @Fintype.card {f : Fin n → Fin n // P f} CategoryTheory.FinCategory.fintypeObj =
        @Fintype.card {f : Fin n → Fin n // P f} (Subtype.fintype P) := by
          exact @Fintype.card_congr {f : Fin n → Fin n // P f} {f : Fin n → Fin n // P f}
            CategoryTheory.FinCategory.fintypeObj (Subtype.fintype P) (Equiv.refl _)
    _ = Fintype.card (CycleFiberData x₀ (k - 1)) := by
          simpa [P, hsucc] using card_firstReturnFiber_length (n := n) (l := k - 1) x₀
    _ = (n - 1).descFactorial (k - 1) * n ^ (n - k) := by
          exact card_cycleFiberData_of_mem_Icc x₀ hk

theorem card_periodicAt {n : ℕ} (x₀ : Fin n) (hn : 0 < n) :
    Fintype.card {f : Fin n → Fin n // PeriodicPoint f x₀}
      = ∑ k ∈ Finset.Icc 1 n, (n - 1).descFactorial (k - 1) * n ^ (n - k) := by
  classical
  let P : (Fin n → Fin n) → Prop := fun f => PeriodicPoint f x₀
  let A : Type := {f : Fin n → Fin n // P f}
  let B : Type := {k : ℕ // k ∈ Finset.Icc 1 n}
  letI : Fintype A := Subtype.fintype P
  letI : Fintype B := by
    dsimp [B]
    infer_instance
  let idx : A → B := firstReturnIndex x₀ hn
  change @Fintype.card A CategoryTheory.FinCategory.fintypeObj =
    ∑ k ∈ Finset.Icc 1 n, (n - 1).descFactorial (k - 1) * n ^ (n - k)
  calc
    @Fintype.card A CategoryTheory.FinCategory.fintypeObj =
        @Fintype.card A (Subtype.fintype P) := by
          exact @Fintype.card_congr A A CategoryTheory.FinCategory.fintypeObj
            (Subtype.fintype P) (Equiv.refl A)
    _ = ∑ K : B, Fintype.card {F : A // idx F = K} := by
          exact ForestCountNS.Complete.card_eq_sum_fintype_fiber idx
    _ = ∑ K : B, (n - 1).descFactorial (K.1 - 1) * n ^ (n - K.1) := by
          refine Finset.sum_congr rfl ?_
          intro K _
          change Fintype.card
              {F : {f : Fin n → Fin n // PeriodicPoint f x₀} //
                firstReturnIndex x₀ hn F = K} =
            (n - 1).descFactorial (K.1 - 1) * n ^ (n - K.1)
          let Q : (Fin n → Fin n) → Prop :=
            fun f => f^[K.1] x₀ = x₀ ∧
              ∀ m : ℕ, 0 < m → m < K.1 → f^[m] x₀ ≠ x₀
          calc
            Fintype.card
                {F : {f : Fin n → Fin n // PeriodicPoint f x₀} //
                  firstReturnIndex x₀ hn F = K} =
                @Fintype.card {f : Fin n → Fin n // Q f} (Subtype.fintype Q) := by
                  exact Fintype.card_congr (firstReturnIndexFiberEquiv x₀ hn K)
            _ = @Fintype.card {f : Fin n → Fin n // Q f}
                  CategoryTheory.FinCategory.fintypeObj := by
                  exact @Fintype.card_congr {f : Fin n → Fin n // Q f}
                    {f : Fin n → Fin n // Q f} (Subtype.fintype Q)
                    CategoryTheory.FinCategory.fintypeObj (Equiv.refl _)
            _ = (n - 1).descFactorial (K.1 - 1) * n ^ (n - K.1) := by
                  simpa [Q] using card_firstReturnFiber x₀ K.2
    _ = ∑ k ∈ Finset.Icc 1 n, (n - 1).descFactorial (k - 1) * n ^ (n - k) := by
          let s := Finset.Icc 1 n
          simpa [B, s] using
            (Finset.sum_attach s
              (fun k : ℕ => (n - 1).descFactorial (k - 1) * n ^ (n - k)))

lemma periodicSubtype_card_eq_finset_card {n : ℕ} (f : Fin n → Fin n) :
    Fintype.card {x : Fin n // PeriodicPoint f x} = (periodicPointsFinset f).card := by
  classical
  rw [Fintype.card_subtype]
  simp [periodicPointsFinset]

lemma sum_periodicPointsFinset_card_eq_sum_periodicAt_nat (n : ℕ) :
    (∑ f : Fin n → Fin n, (periodicPointsFinset f).card) =
      ∑ x : Fin n,
        @Fintype.card {f : Fin n → Fin n // PeriodicPoint f x}
          CategoryTheory.FinCategory.fintypeObj := by
  classical
  calc
    (∑ f : Fin n → Fin n, (periodicPointsFinset f).card) =
        ∑ f : Fin n → Fin n,
          Fintype.card {x : Fin n // PeriodicPoint f x} := by
          refine Finset.sum_congr rfl ?_
          intro f _
          calc
            (periodicPointsFinset f).card =
                @Fintype.card {x : Fin n // PeriodicPoint f x}
                  CategoryTheory.FinCategory.fintypeObj := by
                  exact (periodicSubtype_card_eq_finset_card f).symm
            _ = @Fintype.card {x : Fin n // PeriodicPoint f x}
                  (Subtype.fintype (fun x : Fin n => PeriodicPoint f x)) := by
                  exact @Fintype.card_congr {x : Fin n // PeriodicPoint f x}
                    {x : Fin n // PeriodicPoint f x}
                    CategoryTheory.FinCategory.fintypeObj
                    (Subtype.fintype (fun x : Fin n => PeriodicPoint f x)) (Equiv.refl _)
    _ = Fintype.card (Sigma fun f : Fin n → Fin n =>
          {x : Fin n // PeriodicPoint f x}) := by
          exact Fintype.card_sigma.symm
    _ = Fintype.card (Sigma fun x : Fin n =>
          {f : Fin n → Fin n // PeriodicPoint f x}) := by
          exact Fintype.card_congr (periodicPairSwapEquiv n)
    _ = ∑ x : Fin n,
          @Fintype.card {f : Fin n → Fin n // PeriodicPoint f x}
            (Subtype.fintype (fun f : Fin n → Fin n => PeriodicPoint f x)) := by
          exact Fintype.card_sigma
    _ = ∑ x : Fin n,
          @Fintype.card {f : Fin n → Fin n // PeriodicPoint f x}
            CategoryTheory.FinCategory.fintypeObj := by
          refine Finset.sum_congr rfl ?_
          intro x _
          exact @Fintype.card_congr
            {f : Fin n → Fin n // PeriodicPoint f x}
            {f : Fin n → Fin n // PeriodicPoint f x}
            (Subtype.fintype (fun f : Fin n → Fin n => PeriodicPoint f x))
            CategoryTheory.FinCategory.fintypeObj (Equiv.refl _)

lemma sum_periodicPointsFinset_card_eq_sum_periodicAt (n : ℕ) :
    (∑ f : Fin n → Fin n, ((periodicPointsFinset f).card : ℝ)) =
      ∑ x : Fin n,
        (@Fintype.card {f : Fin n → Fin n // PeriodicPoint f x}
          CategoryTheory.FinCategory.fintypeObj : ℝ) := by
  exact_mod_cast sum_periodicPointsFinset_card_eq_sum_periodicAt_nat n

lemma periodicAt_sum_eq_q_scaled {n : ℕ} (hn : 0 < n) :
    (((∑ k ∈ Finset.Icc 1 n,
        (n - 1).descFactorial (k - 1) * n ^ (n - k)) : ℕ) : ℝ) =
      (n : ℝ) ^ (n - 1) *
        AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.ramanujanQ n := by
  calc
    (((∑ k ∈ Finset.Icc 1 n,
        (n - 1).descFactorial (k - 1) * n ^ (n - k)) : ℕ) : ℝ) =
        (Fintype.card {f : Fin n → Fin n // MappingConnected f} : ℝ) := by
          rw [card_connectedMappings hn]
    _ = (n : ℝ) ^ (n - 1) *
          AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.ramanujanQ n := by
          exact card_connectedMappings_eq_q hn

theorem expected_cyclicPoints_eq_q {n : ℕ} (hn : 0 < n) :
    (∑ f : Fin n → Fin n, ((periodicPointsFinset f).card : ℝ)) / (n : ℝ)^n =
      AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.ramanujanQ n := by
  classical
  let S : ℕ :=
    ∑ k ∈ Finset.Icc 1 n,
      (n - 1).descFactorial (k - 1) * n ^ (n - k)
  have hdouble :
      (∑ f : Fin n → Fin n, ((periodicPointsFinset f).card : ℝ)) =
        (n : ℝ) * (S : ℝ) := by
    rw [sum_periodicPointsFinset_card_eq_sum_periodicAt n]
    have hpoint :
        ∀ x : Fin n,
          (@Fintype.card {f : Fin n → Fin n // PeriodicPoint f x}
            CategoryTheory.FinCategory.fintypeObj : ℝ) = (S : ℝ) := by
      intro x
      exact congrArg Nat.cast (card_periodicAt x hn)
    calc
      (∑ x : Fin n,
          (@Fintype.card {f : Fin n → Fin n // PeriodicPoint f x}
            CategoryTheory.FinCategory.fintypeObj : ℝ)) =
          ∑ _x : Fin n, (S : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            exact hpoint x
      _ = (n : ℝ) * (S : ℝ) := by
            simp [Fintype.card_fin]
  have hS :
      (S : ℝ) =
        (n : ℝ) ^ (n - 1) *
          AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.ramanujanQ n := by
    simpa [S] using periodicAt_sum_eq_q_scaled hn
  have hnne : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  have hpow_ne : (n : ℝ) ^ (n - 1) ≠ 0 := pow_ne_zero (n - 1) hnne
  have hpow : (n : ℝ) ^ n = (n : ℝ) * (n : ℝ) ^ (n - 1) := by
    have hsplit : n = 1 + (n - 1) := by omega
    calc
      (n : ℝ) ^ n = (n : ℝ) ^ (1 + (n - 1)) := by
        exact congrArg (fun e : ℕ => (n : ℝ) ^ e) hsplit
      _ = (n : ℝ) * (n : ℝ) ^ (n - 1) := by
        rw [pow_add, pow_one]
  calc
    (∑ f : Fin n → Fin n, ((periodicPointsFinset f).card : ℝ)) / (n : ℝ)^n =
        ((n : ℝ) * (S : ℝ)) / (n : ℝ)^n := by rw [hdouble]
    _ = ((n : ℝ) * ((n : ℝ) ^ (n - 1) *
          AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.ramanujanQ n)) /
          ((n : ℝ) * (n : ℝ) ^ (n - 1)) := by
          rw [hS, hpow]
    _ = AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.ramanujanQ n := by
          field_simp [hnne, hpow_ne]

end
end AnalyticCombinatorics.Ch2.Mappings.CyclicPointsNS

open AnalyticCombinatorics AnalyticCombinatorics.Ch2 AnalyticCombinatorics.Ch2.Mappings AnalyticCombinatorics.Ch2.Mappings.CyclicPointsNS
open Filter Asymptotics
open scoped BigOperators Topology
open AnalyticCombinatorics.Ch2.Mappings.ConnectedMappingsNS
theorem solution :
    (fun n : ℕ => (∑ f : Fin n → Fin n, ((periodicPointsFinset f).card : ℝ)) / (n:ℝ)^n)
      ~[atTop] (fun n : ℕ => Real.sqrt (Real.pi * n / 2)) := by
  classical
  have hevent :
      (fun n : ℕ =>
        (∑ f : Fin n → Fin n, ((periodicPointsFinset f).card : ℝ)) / (n : ℝ)^n)
        =ᶠ[atTop]
      (fun n : ℕ => AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.ramanujanQ n) := by
    exact Filter.eventually_atTop.2 ⟨1, fun n hnge => by
      have hn : 0 < n := by omega
      exact expected_cyclicPoints_eq_q hn⟩
  exact
    (AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.Sharp.ramanujanQ_isEquivalent).congr_left
      hevent.symm
