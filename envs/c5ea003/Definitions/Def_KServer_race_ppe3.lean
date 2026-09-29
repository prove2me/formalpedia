-- Prove2me | Definitions.Def_KServer_race_ppe3
-- name    : KServer_race_ppe3
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-02T01:32:03.478683+00:00
-- url     : https://prove2.me/theorems/1b656431-be72-47de-ac9a-9695badf1802
-- title:
--   Race tail atoms, conditionals, and Doob increments
-- statement:
--   Structure of the race probability space at pure tail depths. The atom of the race filtration at a tail depth is the product of an adversary head atom, the frozen coin outcome, side-path atoms at the revealed depths revL2/revR2, and a coin-cost atom at revC (tail_atom_mem). Sums of product-form functions over a tail atom factor into the product of the component atom sums against the frozen coin weight (tail_atom_sum). Consequently the race conditional expectation of a sum F(l) + G(r) + H(cc) at a tail depth splits into the three component conditional expectations at the revealed depths (race_cond_tail), and the race Doob increment of the race tail mass at a pure tail depth equals the branch-selected side conditional-expectation revision plus the coin-cost revision (race_dinc_tail); the dead branch contributes a constant whose revision vanishes.
-- source:
--   Bartal-Chrobak-Rasala lower bound program: prophecy energy for races

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_race_sched
import Definitions.Def_KServer_race_coin
import Definitions.Def_KServer_race_core
import Definitions.Def_KServer_race_hist
import Definitions.Def_KServer_race_total
import Definitions.Def_KServer_race_exp
import Definitions.Def_KServer_race_var3
import Definitions.Def_KServer_sturdy
import Definitions.Def_KServer_prophecy
import Definitions.Def_KServer_prophecy2
import Definitions.Def_KServer_prophecyW
import Definitions.Def_KServer_race_ppe1
import Definitions.Def_KServer_race_ppe2

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3200000

namespace KServer

namespace Race

variable {X : Type*} [MetricSpace X]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}

section TailAtom

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ) (ε : ℝ)

/-- Tail-phase atoms of the race filtration are products: the head atom
at full depth, the exact coin word, and side/continuation atoms at the
coin-determined revelation depths. -/
theorem tail_atom_mem (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    {n : ℕ} (hn : A.m + κ < n) (ω ω' : RΩ A BL BR CC κ) :
    rhist2 A BL BR CC κ ω' n = rhist2 A BL BR CC κ ω n
    ↔ A.hist A.m ω'.1 = A.hist A.m ω.1
      ∧ ω'.2.2.2.2 = ω.2.2.2.2
      ∧ BL.hist (revL2 A BL BR CC κ ω (n - A.m - κ)) ω'.2.1
          = BL.hist (revL2 A BL BR CC κ ω (n - A.m - κ)) ω.2.1
      ∧ BR.hist (revR2 A BL BR CC κ ω (n - A.m - κ)) ω'.2.2.1
          = BR.hist (revR2 A BL BR CC κ ω (n - A.m - κ)) ω.2.2.1
      ∧ CC.hist (revC A BL BR CC κ ω (n - A.m - κ)) ω'.2.2.2.1
          = CC.hist (revC A BL BR CC κ ω (n - A.m - κ)) ω.2.2.2.1 := by
  have hcntL : cntL ω.2.2.2.2 κ ≤ revL2 A BL BR CC κ ω (n - A.m - κ) := by
    unfold revL2
    have h1 := cntL_le ω.2.2.2.2 (le_refl κ)
    omega
  have hcntR : cntR ω.2.2.2.2 κ ≤ revR2 A BL BR CC κ ω (n - A.m - κ) := by
    unfold revR2
    have h1 := cntR_le ω.2.2.2.2 (le_refl κ)
    omega
  rw [rhist2_tail A BL BR CC κ ω' hn, rhist2_tail A BL BR CC κ ω hn]
  rw [Nat.pair_eq_pair, Nat.pair_eq_pair, Nat.pair_eq_pair,
    Nat.pair_eq_pair, Nat.pair_eq_pair]
  constructor
  · rintro ⟨-, hA, hcc, hL, hR, hC⟩
    have hχ : ω'.2.2.2.2 = ω.2.2.2.2 := by
      funext i
      exact coinCode_inj hcc i i.isLt
    have hrevL : revL2 A BL BR CC κ ω' (n - A.m - κ)
        = revL2 A BL BR CC κ ω (n - A.m - κ) := by
      unfold revL2
      rw [hχ]
    have hrevR : revR2 A BL BR CC κ ω' (n - A.m - κ)
        = revR2 A BL BR CC κ ω (n - A.m - κ) := by
      unfold revR2
      rw [hχ]
    rw [hrevL] at hL
    rw [hrevR] at hR
    have hcntL' : cntL ω'.2.2.2.2 κ
        ≤ revL2 A BL BR CC κ ω (n - A.m - κ) := by
      rw [hχ]
      exact hcntL
    have hcntR' : cntR ω'.2.2.2.2 κ
        ≤ revR2 A BL BR CC κ ω (n - A.m - κ) := by
      rw [hχ]
      exact hcntR
    have hrevC : revC A BL BR CC κ ω' (n - A.m - κ)
        = revC A BL BR CC κ ω (n - A.m - κ) :=
      revC_congr A BL BR CC κ hχ hcntL' hcntR' hL hR _
    rw [hrevC] at hC
    exact ⟨hA, hχ, hL, hR, hC⟩
  · rintro ⟨hA, hχ, hL, hR, hC⟩
    have hrevL : revL2 A BL BR CC κ ω' (n - A.m - κ)
        = revL2 A BL BR CC κ ω (n - A.m - κ) := by
      unfold revL2
      rw [hχ]
    have hrevR : revR2 A BL BR CC κ ω' (n - A.m - κ)
        = revR2 A BL BR CC κ ω (n - A.m - κ) := by
      unfold revR2
      rw [hχ]
    have hcntL' : cntL ω'.2.2.2.2 κ
        ≤ revL2 A BL BR CC κ ω (n - A.m - κ) := by
      rw [hχ]
      exact hcntL
    have hcntR' : cntR ω'.2.2.2.2 κ
        ≤ revR2 A BL BR CC κ ω (n - A.m - κ) := by
      rw [hχ]
      exact hcntR
    have hrevC : revC A BL BR CC κ ω' (n - A.m - κ)
        = revC A BL BR CC κ ω (n - A.m - κ) :=
      revC_congr A BL BR CC κ hχ hcntL' hcntR' hL hR _
    refine ⟨rfl, hA, by rw [hχ], ?_, ?_, ?_⟩
    · rw [hrevL]
      exact hL
    · rw [hrevR]
      exact hR
    · rw [hrevC]
      exact hC

/-- Counting along a restricted path matches the full path. -/
theorem cntL_restrict' {κ' : ℕ} (χ : Fin κ' → Bool) {j : ℕ} (hj : j ≤ κ') :
    cntL (restrict χ j hj) j = cntL χ j := by
  unfold cntL
  refine congrArg Finset.card (Finset.filter_congr fun i hi => ?_)
  simp only [Finset.mem_range] at hi
  unfold restrict
  constructor
  · intro h1 hi2
    exact h1 hi
  · intro h1 hi2
    exact h1 (by omega)

theorem cntR_restrict' {κ' : ℕ} (χ : Fin κ' → Bool) {j : ℕ} (hj : j ≤ κ') :
    cntR (restrict χ j hj) j = cntR χ j := by
  unfold cntR
  refine congrArg Finset.card (Finset.filter_congr fun i hi => ?_)
  simp only [Finset.mem_range] at hi
  unfold restrict
  constructor
  · intro h1 hi2
    exact h1 hi
  · intro h1 hi2
    exact h1 (by omega)

/-- The coin-path weight along `χ` is determined by the left side's
history at the consumed count. -/
theorem coinWt_congr_path_l (a : A.Ω) {l l' : BL.Ω} (r : BR.Ω)
    (χ : Fin κ → Bool) {NL : ℕ} (hNL : cntL χ κ ≤ NL)
    (hl : BL.hist NL l' = BL.hist NL l) :
    coinWt (coinW A BL BR a l' r (ε := ε)) χ
      = coinWt (coinW A BL BR a l r (ε := ε)) χ := by
  unfold coinWt
  refine Finset.prod_congr rfl fun j _ => ?_
  unfold coinW
  have hfun : (fun i : Fin (j : ℕ) =>
      restrict χ (j : ℕ) (le_of_lt j.isLt) i)
      = restrict χ (j : ℕ) (le_of_lt j.isLt) := rfl
  have hsz : BL.sizeN (cntL (fun i : Fin (j : ℕ) =>
        restrict χ (j : ℕ) (le_of_lt j.isLt) i) (j : ℕ)) l'
      = BL.sizeN (cntL (fun i : Fin (j : ℕ) =>
        restrict χ (j : ℕ) (le_of_lt j.isLt) i) (j : ℕ)) l := by
    rw [hfun, cntL_restrict' χ (le_of_lt j.isLt)]
    exact sizeN_congr_le BL
      (le_trans (cntL_mono χ (le_of_lt j.isLt)) hNL) hl
  simp only [hsz]

theorem coinWt_congr_path_r (a : A.Ω) (l : BL.Ω) {r r' : BR.Ω}
    (χ : Fin κ → Bool) {NR : ℕ} (hNR : cntR χ κ ≤ NR)
    (hr : BR.hist NR r' = BR.hist NR r) :
    coinWt (coinW A BL BR a l r' (ε := ε)) χ
      = coinWt (coinW A BL BR a l r (ε := ε)) χ := by
  unfold coinWt
  refine Finset.prod_congr rfl fun j _ => ?_
  unfold coinW
  have hfun : (fun i : Fin (j : ℕ) =>
      restrict χ (j : ℕ) (le_of_lt j.isLt) i)
      = restrict χ (j : ℕ) (le_of_lt j.isLt) := rfl
  have hsz : BR.sizeN (cntR (fun i : Fin (j : ℕ) =>
        restrict χ (j : ℕ) (le_of_lt j.isLt) i) (j : ℕ)) r'
      = BR.sizeN (cntR (fun i : Fin (j : ℕ) =>
        restrict χ (j : ℕ) (le_of_lt j.isLt) i) (j : ℕ)) r := by
    rw [hfun, cntR_restrict' χ (le_of_lt j.isLt)]
    exact sizeN_congr_le BR
      (le_trans (cntR_mono χ (le_of_lt j.isLt)) hNR) hr
  simp only [hsz]

open Classical in
/-- **Tail-atom product factorization**: the restricted race sum of a
product of per-coordinate functions over a tail-phase atom factorizes
into the coordinate atom sums times the frozen coin weight. -/
theorem tail_atom_sum (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    {n : ℕ} (hn : A.m + κ < n) (ω : RΩ A BL BR CC κ)
    (F : BL.Ω → ℝ) (G : BR.Ω → ℝ) (H : CC.Ω → ℝ) :
    ∑ ω' ∈ Finset.univ.filter (fun ω' : RΩ A BL BR CC κ =>
        rhist2 A BL BR CC κ ω' n = rhist2 A BL BR CC κ ω n),
      RP A BL BR CC κ ε ω' * (F ω'.2.1 * (G ω'.2.2.1 * H ω'.2.2.2.1))
    = (∑ a ∈ A.atom A.m ω.1, A.P a)
      * ((∑ l ∈ BL.atom (revL2 A BL BR CC κ ω (n - A.m - κ)) ω.2.1,
            BL.P l * F l)
        * ((∑ r ∈ BR.atom (revR2 A BL BR CC κ ω (n - A.m - κ)) ω.2.2.1,
              BR.P r * G r)
          * ((∑ cc ∈ CC.atom (revC A BL BR CC κ ω (n - A.m - κ))
                ω.2.2.2.1, CC.P cc * H cc)
            * coinWt (coinW A BL BR ω.1 ω.2.1 ω.2.2.1 (ε := ε))
                ω.2.2.2.2))) := by
  set kk := n - A.m - κ with hkk
  set dL := revL2 A BL BR CC κ ω kk with hdL
  set dR := revR2 A BL BR CC κ ω kk with hdR
  set dC := revC A BL BR CC κ ω kk with hdC
  have hcntL : cntL ω.2.2.2.2 κ ≤ dL := by
    rw [hdL]
    unfold revL2
    have h1 := cntL_le ω.2.2.2.2 (le_refl κ)
    omega
  have hcntR : cntR ω.2.2.2.2 κ ≤ dR := by
    rw [hdR]
    unfold revR2
    have h1 := cntR_le ω.2.2.2.2 (le_refl κ)
    omega
  rw [Finset.sum_filter, sum_RΩ_expand A BL BR CC κ
    (fun ω' => if rhist2 A BL BR CC κ ω' n = rhist2 A BL BR CC κ ω n
      then RP A BL BR CC κ ε ω'
        * (F ω'.2.1 * (G ω'.2.2.1 * H ω'.2.2.2.1)) else 0)]
  have hstep : ∀ (a : A.Ω) (l : BL.Ω) (r : BR.Ω) (cc : CC.Ω),
      (∑ χ' : Fin κ → Bool,
        if rhist2 A BL BR CC κ (a, l, r, cc, χ') n
            = rhist2 A BL BR CC κ ω n
        then RP A BL BR CC κ ε (a, l, r, cc, χ')
          * (F l * (G r * H cc)) else 0)
      = (if A.hist A.m a = A.hist A.m ω.1 then A.P a else 0)
        * ((if BL.hist dL l = BL.hist dL ω.2.1 then BL.P l * F l else 0)
          * ((if BR.hist dR r = BR.hist dR ω.2.2.1
              then BR.P r * G r else 0)
            * ((if CC.hist dC cc = CC.hist dC ω.2.2.2.1
                then CC.P cc * H cc else 0)
              * coinWt (coinW A BL BR ω.1 ω.2.1 ω.2.2.1 (ε := ε))
                  ω.2.2.2.2))) := by
    intro a l r cc
    rw [Finset.sum_eq_single ω.2.2.2.2]
    · by_cases hcond : A.hist A.m a = A.hist A.m ω.1
        ∧ BL.hist dL l = BL.hist dL ω.2.1
        ∧ BR.hist dR r = BR.hist dR ω.2.2.1
        ∧ CC.hist dC cc = CC.hist dC ω.2.2.2.1
      · obtain ⟨hA, hL, hR, hC⟩ := hcond
        have hmem : rhist2 A BL BR CC κ (a, l, r, cc, ω.2.2.2.2) n
            = rhist2 A BL BR CC κ ω n := by
          rw [tail_atom_mem A BL BR CC κ hκL hκR hn ω _]
          exact ⟨hA, rfl, hL, hR, hC⟩
        rw [if_pos hmem, if_pos hA, if_pos hL, if_pos hR, if_pos hC]
        have hcw : coinWt (coinW A BL BR a l r (ε := ε)) ω.2.2.2.2
            = coinWt (coinW A BL BR ω.1 ω.2.1 ω.2.2.1 (ε := ε))
                ω.2.2.2.2 := by
          rw [coinW_indep A BL BR ε a ω.1 l r,
            coinWt_congr_path_l A BL BR κ ε ω.1 r ω.2.2.2.2
              hcntL hL,
            coinWt_congr_path_r A BL BR κ ε ω.1 ω.2.1 ω.2.2.2.2
              hcntR hR]
        show RP A BL BR CC κ ε (a, l, r, cc, ω.2.2.2.2)
            * (F l * (G r * H cc)) = _
        unfold RP
        rw [hcw]
        ring
      · have hnotmem : ¬ rhist2 A BL BR CC κ (a, l, r, cc, ω.2.2.2.2) n
            = rhist2 A BL BR CC κ ω n := by
          intro hmem
          rw [tail_atom_mem A BL BR CC κ hκL hκR hn ω _] at hmem
          exact hcond ⟨hmem.1, hmem.2.2.1, hmem.2.2.2.1, hmem.2.2.2.2⟩
        rw [if_neg hnotmem]
        by_cases hA : A.hist A.m a = A.hist A.m ω.1
        · rw [if_pos hA]
          by_cases hL : BL.hist dL l = BL.hist dL ω.2.1
          · rw [if_pos hL]
            by_cases hR : BR.hist dR r = BR.hist dR ω.2.2.1
            · rw [if_pos hR]
              have hC : ¬ CC.hist dC cc = CC.hist dC ω.2.2.2.1 :=
                fun hC => hnotmem (by
                  rw [tail_atom_mem A BL BR CC κ hκL hκR hn ω _]
                  exact ⟨hA, rfl, hL, hR, hC⟩)
              rw [if_neg hC]
              ring
            · rw [if_neg hR]
              ring
          · rw [if_neg hL]
            ring
        · rw [if_neg hA]
          ring
    · intro χ' _ hne
      rw [if_neg]
      intro hmem
      rw [tail_atom_mem A BL BR CC κ hκL hκR hn ω _] at hmem
      exact hne hmem.2.1
    · intro hc
      exact absurd (Finset.mem_univ _) hc
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun cc _ =>
      hstep a l r cc]
  -- factor the four indicator sums, innermost first
  have hC1 : ∑ cc : CC.Ω,
      (if CC.hist dC cc = CC.hist dC ω.2.2.2.1 then CC.P cc * H cc else 0)
      = ∑ cc ∈ CC.atom dC ω.2.2.2.1, CC.P cc * H cc := by
    rw [← Finset.sum_filter]
    rfl
  have hR1 : ∑ r : BR.Ω,
      (if BR.hist dR r = BR.hist dR ω.2.2.1 then BR.P r * G r else 0)
      = ∑ r ∈ BR.atom dR ω.2.2.1, BR.P r * G r := by
    rw [← Finset.sum_filter]
    rfl
  have hL1 : ∑ l : BL.Ω,
      (if BL.hist dL l = BL.hist dL ω.2.1 then BL.P l * F l else 0)
      = ∑ l ∈ BL.atom dL ω.2.1, BL.P l * F l := by
    rw [← Finset.sum_filter]
    rfl
  have hA1 : ∑ a : A.Ω,
      (if A.hist A.m a = A.hist A.m ω.1 then A.P a else 0)
      = ∑ a ∈ A.atom A.m ω.1, A.P a := by
    rw [← Finset.sum_filter]
    rfl
  rw [← hA1, ← hL1, ← hR1, ← hC1]
  set cw := coinWt (coinW A BL BR ω.1 ω.2.1 ω.2.2.1 (ε := ε)) ω.2.2.2.2
    with hcw_def
  set IA : A.Ω → ℝ := fun a =>
    if A.hist A.m a = A.hist A.m ω.1 then A.P a else 0 with hIA
  set IL : BL.Ω → ℝ := fun l =>
    if BL.hist dL l = BL.hist dL ω.2.1 then BL.P l * F l else 0 with hIL
  set IR : BR.Ω → ℝ := fun r =>
    if BR.hist dR r = BR.hist dR ω.2.2.1 then BR.P r * G r else 0
    with hIR
  set IC : CC.Ω → ℝ := fun cc =>
    if CC.hist dC cc = CC.hist dC ω.2.2.2.1 then CC.P cc * H cc else 0
    with hIC
  show ∑ a : A.Ω, ∑ l : BL.Ω, ∑ r : BR.Ω, ∑ cc : CC.Ω,
      IA a * (IL l * (IR r * (IC cc * cw)))
    = (∑ a : A.Ω, IA a) * ((∑ l : BL.Ω, IL l)
        * ((∑ r : BR.Ω, IR r) * ((∑ cc : CC.Ω, IC cc) * cw)))
  rw [show (∑ a : A.Ω, IA a) * ((∑ l : BL.Ω, IL l)
      * ((∑ r : BR.Ω, IR r) * ((∑ cc : CC.Ω, IC cc) * cw)))
    = ∑ a : A.Ω, ∑ l : BL.Ω, ∑ r : BR.Ω, ∑ cc : CC.Ω,
        IA a * (IL l * (IR r * (IC cc * cw))) from by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show (∑ l : BL.Ω, IL l) * ((∑ r : BR.Ω, IR r)
        * ((∑ cc : CC.Ω, IC cc) * cw))
      = ∑ l : BL.Ω, IL l * ((∑ r : BR.Ω, IR r)
          * ((∑ cc : CC.Ω, IC cc) * cw)) from by rw [Finset.sum_mul],
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [show (∑ r : BR.Ω, IR r) * ((∑ cc : CC.Ω, IC cc) * cw)
      = ∑ r : BR.Ω, IR r * ((∑ cc : CC.Ω, IC cc) * cw)
        from by rw [Finset.sum_mul],
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [show (∑ cc : CC.Ω, IC cc) * cw
      = ∑ cc : CC.Ω, IC cc * cw from by rw [Finset.sum_mul],
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]]

open Classical in
/-- **Race conditionals at tail depths split by coordinate**: the race
conditional of a sum of per-coordinate functions over a tail-phase atom
is the sum of the coordinate conditionals at the revelation depths. -/
theorem race_cond_tail (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    {n : ℕ} (hn : A.m + κ < n) (ω : RΩ A BL BR CC κ)
    (F : BL.Ω → ℝ) (G : BR.Ω → ℝ) (H : CC.Ω → ℝ) :
    rcond A BL BR CC κ ε
        (fun ω' => F ω'.2.1 + G ω'.2.2.1 + H ω'.2.2.2.1) n ω
      = BL.condExp F (revL2 A BL BR CC κ ω (n - A.m - κ)) ω.2.1
        + BR.condExp G (revR2 A BL BR CC κ ω (n - A.m - κ)) ω.2.2.1
        + CC.condExp H (revC A BL BR CC κ ω (n - A.m - κ)) ω.2.2.2.1 := by
  set kk := n - A.m - κ with hkk
  set dL := revL2 A BL BR CC κ ω kk with hdL
  set dR := revR2 A BL BR CC κ ω kk with hdR
  set dC := revC A BL BR CC κ ω kk with hdC
  set cw := coinWt (coinW A BL BR ω.1 ω.2.1 ω.2.2.1 (ε := ε)) ω.2.2.2.2
    with hcw_def
  have hcw : 0 < cw := by
    rw [hcw_def]
    refine coinWt_pos (fun j p b => ?_) _
    unfold coinW
    by_cases hb : b
    · rw [if_pos hb]
      exact probL_pos hε
    · rw [if_neg hb]
      exact probL_pos hε
  set mA := ∑ a ∈ A.atom A.m ω.1, A.P a with hmA
  set mL := ∑ l ∈ BL.atom dL ω.2.1, BL.P l with hmL
  set mR := ∑ r ∈ BR.atom dR ω.2.2.1, BR.P r with hmR
  set mC := ∑ cc ∈ CC.atom dC ω.2.2.2.1, CC.P cc with hmC
  set SF := ∑ l ∈ BL.atom dL ω.2.1, BL.P l * F l with hSF
  set SG := ∑ r ∈ BR.atom dR ω.2.2.1, BR.P r * G r with hSG
  set SC := ∑ cc ∈ CC.atom dC ω.2.2.2.1, CC.P cc * H cc with hSC
  have hmA0 : 0 < mA := A.mass_atom_pos A.m ω.1
  have hmL0 : 0 < mL := BL.mass_atom_pos dL ω.2.1
  have hmR0 : 0 < mR := BR.mass_atom_pos dR ω.2.2.1
  have hmC0 : 0 < mC := CC.mass_atom_pos dC ω.2.2.2.1
  -- the three numerator components and the denominator
  have hFsum := tail_atom_sum A BL BR CC κ ε hε hκL hκR hn ω
    F (fun _ => 1) (fun _ => 1)
  have hGsum := tail_atom_sum A BL BR CC κ ε hε hκL hκR hn ω
    (fun _ => 1) G (fun _ => 1)
  have hHsum := tail_atom_sum A BL BR CC κ ε hε hκL hκR hn ω
    (fun _ => 1) (fun _ => 1) H
  have hDsum := tail_atom_sum A BL BR CC κ ε hε hκL hκR hn ω
    (fun _ => 1) (fun _ => 1) (fun _ => 1)
  have hone : ∀ (Y : Type) [Fintype Y] (P' : Y → ℝ) (S : Finset Y),
      ∑ y ∈ S, P' y * (fun _ : Y => (1 : ℝ)) y = ∑ y ∈ S, P' y := by
    intro Y _ P' S
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hone BL.Ω BL.P] at hGsum hHsum hDsum
  rw [hone BR.Ω BR.P] at hFsum hHsum hDsum
  rw [hone CC.Ω CC.P] at hFsum hGsum hDsum
  have hnum : ∑ ω' ∈ Finset.univ.filter (fun ω' : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω' n = rhist2 A BL BR CC κ ω n),
      RP A BL BR CC κ ε ω'
        * (F ω'.2.1 + G ω'.2.2.1 + H ω'.2.2.2.1)
      = mA * (SF * (mR * (mC * cw))) + mA * (mL * (SG * (mC * cw)))
        + mA * (mL * (mR * (SC * cw))) := by
    have hlin : ∑ ω' ∈ Finset.univ.filter (fun ω' : RΩ A BL BR CC κ =>
        rhist2 A BL BR CC κ ω' n = rhist2 A BL BR CC κ ω n),
        RP A BL BR CC κ ε ω'
          * (F ω'.2.1 + G ω'.2.2.1 + H ω'.2.2.2.1)
        = (∑ ω' ∈ Finset.univ.filter (fun ω' : RΩ A BL BR CC κ =>
            rhist2 A BL BR CC κ ω' n = rhist2 A BL BR CC κ ω n),
            RP A BL BR CC κ ε ω'
              * (F ω'.2.1 * ((1 : ℝ) * (1 : ℝ))))
          + (∑ ω' ∈ Finset.univ.filter (fun ω' : RΩ A BL BR CC κ =>
              rhist2 A BL BR CC κ ω' n = rhist2 A BL BR CC κ ω n),
              RP A BL BR CC κ ε ω'
                * ((1 : ℝ) * (G ω'.2.2.1 * (1 : ℝ))))
          + ∑ ω' ∈ Finset.univ.filter (fun ω' : RΩ A BL BR CC κ =>
              rhist2 A BL BR CC κ ω' n = rhist2 A BL BR CC κ ω n),
              RP A BL BR CC κ ε ω'
                * ((1 : ℝ) * ((1 : ℝ) * H ω'.2.2.2.1)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ω' _ => ?_
      ring
    rw [hlin, hFsum, hGsum, hHsum]
  have hden : ∑ ω' ∈ Finset.univ.filter (fun ω' : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω' n = rhist2 A BL BR CC κ ω n),
      RP A BL BR CC κ ε ω'
      = mA * (mL * (mR * (mC * cw))) := by
    rw [← hDsum]
    refine Finset.sum_congr rfl fun ω' _ => ?_
    ring
  show (∑ ω' ∈ Finset.univ.filter (fun ω' : RΩ A BL BR CC κ =>
      rhist2 A BL BR CC κ ω' n = rhist2 A BL BR CC κ ω n),
      RP A BL BR CC κ ε ω'
        * (F ω'.2.1 + G ω'.2.2.1 + H ω'.2.2.2.1))
    / (∑ ω' ∈ Finset.univ.filter (fun ω' : RΩ A BL BR CC κ =>
        rhist2 A BL BR CC κ ω' n = rhist2 A BL BR CC κ ω n),
        RP A BL BR CC κ ε ω')
    = SF / mL + SG / mR + SC / mC
  rw [hnum, hden]
  field_simp

/-- Race conditionals only read atom values. -/
theorem rcond_congr_atom (f g : RΩ A BL BR CC κ → ℝ) {n : ℕ}
    (ω : RΩ A BL BR CC κ)
    (hfg : ∀ ω' : RΩ A BL BR CC κ,
      rhist2 A BL BR CC κ ω' n = rhist2 A BL BR CC κ ω n →
      f ω' = g ω') :
    rcond A BL BR CC κ ε f n ω = rcond A BL BR CC κ ε g n ω := by
  unfold rcond
  congr 1
  refine Finset.sum_congr rfl fun ω' hm => ?_
  rw [Finset.mem_filter] at hm
  rw [hfg ω' hm.2]

/-- Constants shared across a tail atom: the coin word, the survivor
identity and the remaining count. -/
theorem tail_atom_facts (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    {n : ℕ} (hn : A.m + κ < n) {ω ω' : RΩ A BL BR CC κ}
    (hmem : rhist2 A BL BR CC κ ω' n = rhist2 A BL BR CC κ ω n) :
    ω'.2.2.2.2 = ω.2.2.2.2
    ∧ survL A BL BR CC κ ω' = survL A BL BR CC κ ω
    ∧ remCnt A BL BR CC κ ω' = remCnt A BL BR CC κ ω := by
  have h := (tail_atom_mem A BL BR CC κ hκL hκR hn ω ω').mp hmem
  obtain ⟨hA, hχ, hL, hR, hC⟩ := h
  have hcntL : cntL ω'.2.2.2.2 κ ≤ revL2 A BL BR CC κ ω (n - A.m - κ) := by
    rw [hχ]
    unfold revL2
    have h1 := cntL_le ω.2.2.2.2 (le_refl κ)
    omega
  have hcntR : cntR ω'.2.2.2.2 κ ≤ revR2 A BL BR CC κ ω (n - A.m - κ) := by
    rw [hχ]
    unfold revR2
    have h1 := cntR_le ω.2.2.2.2 (le_refl κ)
    omega
  exact ⟨hχ, survL_congr A BL BR CC κ hχ hcntL hcntR hL hR,
    remCnt_congr A BL BR CC κ hχ hcntL hcntR hL hR⟩

open Classical in
/-- **Tail-phase Doob increments split by coordinate**: at a pure
tail-phase depth, the race increment of a deeper race tail is the
selected side's conditional revision plus the continuation's. -/
theorem race_dinc_tail (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    {h e : ℕ} (hh : A.m + κ < h) (he : h < e) (ω : RΩ A BL BR CC κ) :
    rcond A BL BR CC κ ε (rtailN A BL BR CC κ ε e) (h + 1) ω
      - rcond A BL BR CC κ ε (rtailN A BL BR CC κ ε e) h ω
    = (if survL A BL BR CC κ ω then
        BL.condExp (BL.tailSum (cntL ω.2.2.2.2 κ + (e - A.m - κ)))
            (revL2 A BL BR CC κ ω (h + 1 - A.m - κ)) ω.2.1
          - BL.condExp (BL.tailSum (cntL ω.2.2.2.2 κ + (e - A.m - κ)))
            (revL2 A BL BR CC κ ω (h - A.m - κ)) ω.2.1
      else
        BR.condExp (BR.tailSum (cntR ω.2.2.2.2 κ + (e - A.m - κ)))
            (revR2 A BL BR CC κ ω (h + 1 - A.m - κ)) ω.2.2.1
          - BR.condExp (BR.tailSum (cntR ω.2.2.2.2 κ + (e - A.m - κ)))
            (revR2 A BL BR CC κ ω (h - A.m - κ)) ω.2.2.1)
      + (CC.condExp (CC.tailSum
            (max (e - A.m - κ - remCnt A BL BR CC κ ω) 1))
            (revC A BL BR CC κ ω (h + 1 - A.m - κ)) ω.2.2.2.1
          - CC.condExp (CC.tailSum
            (max (e - A.m - κ - remCnt A BL BR CC κ ω) 1))
            (revC A BL BR CC κ ω (h - A.m - κ)) ω.2.2.2.1) := by
  set ke := e - A.m - κ with hke
  have hke1 : 1 ≤ ke := by omega
  -- the on-atom coordinate representation, valid on both depth atoms
  by_cases hs : survL A BL BR CC κ ω
  · set F : BL.Ω → ℝ := BL.tailSum (cntL ω.2.2.2.2 κ + ke) with hF
    set H : CC.Ω → ℝ :=
      CC.tailSum (max (ke - remCnt A BL BR CC κ ω) 1) with hH
    have hrep : ∀ n', A.m + κ < n' →
        rcond A BL BR CC κ ε (rtailN A BL BR CC κ ε e) n' ω
        = rcond A BL BR CC κ ε (fun ω' => F ω'.2.1
            + (fun _ : BR.Ω => (0 : ℝ)) ω'.2.2.1 + H ω'.2.2.2.1) n' ω := by
      intro n' hn'
      refine rcond_congr_atom A BL BR CC κ ε _ _ ω fun ω' hmem => ?_
      obtain ⟨hχ, hsv, hrc⟩ :=
        tail_atom_facts A BL BR CC κ hκL hκR hn' hmem
      have hdec := rtail_tail_decomp A BL BR CC κ ε hκL hκR
        (show 1 ≤ ke by omega) ω'
      rw [show A.m + κ + ke = e from by omega] at hdec
      rw [hdec, if_pos (by rw [hsv]; exact hs), hχ, hrc]
      show BL.tailSum (cntL ω.2.2.2.2 κ + ke) ω'.2.1
          + CC.tailSum (max (ke - remCnt A BL BR CC κ ω) 1) ω'.2.2.2.1
        = F ω'.2.1 + 0 + H ω'.2.2.2.1
      rw [hF, hH]
      ring
    rw [hrep (h + 1) (by omega), hrep h (by omega),
      race_cond_tail A BL BR CC κ ε hε hκL hκR (show A.m + κ < h + 1 by omega) ω
        F (fun _ => 0) H,
      race_cond_tail A BL BR CC κ ε hε hκL hκR hh ω
        F (fun _ => 0) H]
    rw [if_pos hs]
    have hz1 : BR.condExp (fun _ => (0 : ℝ))
        (revR2 A BL BR CC κ ω (h + 1 - A.m - κ)) ω.2.2.1 = 0 :=
      BR.condExp_const 0 _ _
    have hz2 : BR.condExp (fun _ => (0 : ℝ))
        (revR2 A BL BR CC κ ω (h - A.m - κ)) ω.2.2.1 = 0 :=
      BR.condExp_const 0 _ _
    rw [hz1, hz2]
    ring
  · set G : BR.Ω → ℝ := BR.tailSum (cntR ω.2.2.2.2 κ + ke) with hG
    set H : CC.Ω → ℝ :=
      CC.tailSum (max (ke - remCnt A BL BR CC κ ω) 1) with hH
    have hrep : ∀ n', A.m + κ < n' →
        rcond A BL BR CC κ ε (rtailN A BL BR CC κ ε e) n' ω
        = rcond A BL BR CC κ ε (fun ω' =>
            (fun _ : BL.Ω => (0 : ℝ)) ω'.2.1
            + G ω'.2.2.1 + H ω'.2.2.2.1) n' ω := by
      intro n' hn'
      refine rcond_congr_atom A BL BR CC κ ε _ _ ω fun ω' hmem => ?_
      obtain ⟨hχ, hsv, hrc⟩ :=
        tail_atom_facts A BL BR CC κ hκL hκR hn' hmem
      have hdec := rtail_tail_decomp A BL BR CC κ ε hκL hκR
        (show 1 ≤ ke by omega) ω'
      rw [show A.m + κ + ke = e from by omega] at hdec
      rw [hdec, if_neg (by rw [hsv]; exact hs), hχ, hrc]
      show BR.tailSum (cntR ω.2.2.2.2 κ + ke) ω'.2.2.1
          + CC.tailSum (max (ke - remCnt A BL BR CC κ ω) 1) ω'.2.2.2.1
        = 0 + G ω'.2.2.1 + H ω'.2.2.2.1
      rw [hG, hH]
      ring
    rw [hrep (h + 1) (by omega), hrep h (by omega),
      race_cond_tail A BL BR CC κ ε hε hκL hκR (show A.m + κ < h + 1 by omega) ω
        (fun _ => 0) G H,
      race_cond_tail A BL BR CC κ ε hε hκL hκR hh ω
        (fun _ => 0) G H]
    rw [if_neg hs]
    have hz1 : BL.condExp (fun _ => (0 : ℝ))
        (revL2 A BL BR CC κ ω (h + 1 - A.m - κ)) ω.2.1 = 0 :=
      BL.condExp_const 0 _ _
    have hz2 : BL.condExp (fun _ => (0 : ℝ))
        (revL2 A BL BR CC κ ω (h - A.m - κ)) ω.2.1 = 0 :=
      BL.condExp_const 0 _ _
    rw [hz1, hz2]
    ring

end TailAtom

end Race

end KServer


