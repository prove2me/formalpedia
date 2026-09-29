-- Prove2me | Definitions.Def_KServer_race_exp
-- name    : KServer_race_exp
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T18:47:56.071102+00:00
-- url     : https://prove2.me/theorems/dec48c8f-6bc9-4609-99b6-d614977b746d
-- title:
--   Expected race total and variance
-- statement:
--   Expectation-level accounting for the race chunk system. The tower property of the path-dependent coin-tree measure at a single step: for any function $F$ of the coin prefix and the current coin, integrating $F$ against the tree equals integrating its one-step conditional average. Marginalization lemmas expressing race-space expectations of functions of individual coordinates as expectations under the corresponding component measures. Deviation lemmas on finite probability spaces: the expected shortfall $\mathbb{E}\,(T-X)^+$ below a target $T \le \mathbb{E}X$ is at most $\sqrt{V}$ when $\mathrm{Var}(X)\le V$ (Cauchy–Schwarz), and for independent totals $X_1, X_2$ with mean at least $T$ and variance at most $V$,
--   $$\mathbb{E}\min(X_1,X_2) \ge T - 2\sqrt{V}.$$
--   The main results: the expected total size of the race system satisfies
--   $$\mathbb{E}\Big[\sum_r \mathrm{rsize}(r)\Big] \ge 3T + \tfrac{G}{2} - 2c_B - \tfrac{\kappa\varepsilon}{2} - 2\sqrt{V},$$
--   where $G$ is any lower bound on the expected imbalance $\mathbb{E}|S_L - S_R|$ of the consumed side masses; and the variance of the race total is at most $9V + 6c_B^2 + 3\,(2(m_L+m_R)c_B)^2$ by a three-block decomposition (head and closing blocks carry their variances, the side/coin block is bounded by its range).
-- source:
--   BCR randomized k-server lower bound, race construction

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_shadow
import Definitions.Def_KServer_park_shadow
import Definitions.Def_KServer_shadow2
import Definitions.Def_KServer_race_sched
import Definitions.Def_KServer_race_coin
import Definitions.Def_KServer_race_core
import Definitions.Def_KServer_race_hist
import Definitions.Def_KServer_absorb
import Definitions.Def_KServer_race_opt
import Definitions.Def_KServer_race_cost1
import Definitions.Def_KServer_race_cost2
import Definitions.Def_KServer_race_total

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3200000

namespace KServer

namespace Race

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}

section Tower

/-- The tower property of the coin-tree measure at a single step: the coin
at step `j` integrates against its conditional weights. -/
theorem coinWt_tower {j : ℕ} (F : (Fin j → Bool) → Bool → ℝ) :
    ∀ {κ : ℕ} (W : (j' : ℕ) → (Fin j' → Bool) → Bool → ℝ),
      (∀ (j' : ℕ) (p : Fin j' → Bool), W j' p true + W j' p false = 1) →
      ∀ (hj : j < κ),
      ∑ c : Fin κ → Bool,
          coinWt W c * F (restrict c j (le_of_lt hj)) (c ⟨j, hj⟩)
        = ∑ c : Fin κ → Bool,
            coinWt W c
              * (W j (restrict c j (le_of_lt hj)) true
                  * F (restrict c j (le_of_lt hj)) true
                + W j (restrict c j (le_of_lt hj)) false
                  * F (restrict c j (le_of_lt hj)) false) := by
  intro κ
  induction κ with
  | zero =>
    intro W hsum hj
    omega
  | succ n ih =>
    intro W hsum hj
    have hre : ∀ g : (Fin (n + 1) → Bool) → ℝ,
        ∑ c, g c
          = ∑ p : Fin n → Bool, ∑ b : Bool, g ((snocEquiv n).symm (p, b)) := by
      intro g
      rw [← Equiv.sum_comp (snocEquiv n).symm g, Fintype.sum_prod_type]
    rw [hre, hre]
    have hwt : ∀ (p : Fin n → Bool) (b : Bool),
        coinWt W ((snocEquiv n).symm (p, b)) = coinWt W p * W n p b := by
      intro p b
      have h1 : (fun i : Fin n => ((snocEquiv n).symm (p, b)) i.castSucc)
          = p := funext fun i => snocEquiv_symm_castSucc p b i
      rw [coinWt_split_last, h1, snocEquiv_symm_last]
    by_cases hjn : j < n
    · have hres : ∀ (p : Fin n → Bool) (b : Bool),
          restrict ((snocEquiv n).symm (p, b)) j (le_of_lt hj)
            = restrict p j (le_of_lt hjn) := fun p b =>
        restrict_snoc p b j (le_of_lt hjn) (le_of_lt hj)
      have hval : ∀ (p : Fin n → Bool) (b : Bool),
          ((snocEquiv n).symm (p, b)) ⟨j, hj⟩ = p ⟨j, hjn⟩ := by
        intro p b
        show ((snocEquiv n).symm (p, b)) (⟨j, hjn⟩ : Fin n).castSucc
          = p ⟨j, hjn⟩
        exact snocEquiv_symm_castSucc p b ⟨j, hjn⟩
      have hL : ∀ p : Fin n → Bool,
          (∑ b : Bool, coinWt W ((snocEquiv n).symm (p, b))
              * F (restrict ((snocEquiv n).symm (p, b)) j (le_of_lt hj))
                  (((snocEquiv n).symm (p, b)) ⟨j, hj⟩))
            = coinWt W p * F (restrict p j (le_of_lt hjn)) (p ⟨j, hjn⟩) := by
        intro p
        rw [Fintype.sum_bool, hwt p true, hwt p false, hres p true,
          hres p false, hval p true, hval p false]
        linear_combination
          coinWt W p * F (restrict p j (le_of_lt hjn)) (p ⟨j, hjn⟩)
            * hsum n p
      have hR : ∀ p : Fin n → Bool,
          (∑ b : Bool, coinWt W ((snocEquiv n).symm (p, b))
              * (W j (restrict ((snocEquiv n).symm (p, b)) j (le_of_lt hj))
                    true
                  * F (restrict ((snocEquiv n).symm (p, b)) j (le_of_lt hj))
                      true
                + W j (restrict ((snocEquiv n).symm (p, b)) j (le_of_lt hj))
                    false
                  * F (restrict ((snocEquiv n).symm (p, b)) j (le_of_lt hj))
                      false))
            = coinWt W p
                * (W j (restrict p j (le_of_lt hjn)) true
                    * F (restrict p j (le_of_lt hjn)) true
                  + W j (restrict p j (le_of_lt hjn)) false
                    * F (restrict p j (le_of_lt hjn)) false) := by
        intro p
        rw [Fintype.sum_bool, hwt p true, hwt p false, hres p true,
          hres p false]
        linear_combination
          coinWt W p
            * (W j (restrict p j (le_of_lt hjn)) true
                * F (restrict p j (le_of_lt hjn)) true
              + W j (restrict p j (le_of_lt hjn)) false
                * F (restrict p j (le_of_lt hjn)) false)
            * hsum n p
      rw [Finset.sum_congr rfl fun p _ => hL p,
        Finset.sum_congr rfl fun p _ => hR p]
      exact ih W hsum hjn
    · have hjeq : j = n := by omega
      subst hjeq
      have hres : ∀ (p : Fin j → Bool) (b : Bool),
          restrict ((snocEquiv j).symm (p, b)) j (le_of_lt hj) = p := by
        intro p b
        funext i
        show ((snocEquiv j).symm (p, b)) i.castSucc = p i
        exact snocEquiv_symm_castSucc p b i
      have hval : ∀ (p : Fin j → Bool) (b : Bool),
          ((snocEquiv j).symm (p, b)) ⟨j, hj⟩ = b := by
        intro p b
        show ((snocEquiv j).symm (p, b)) (Fin.last j) = b
        exact snocEquiv_symm_last p b
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Fintype.sum_bool, Fintype.sum_bool, hwt p true, hwt p false,
        hres p true, hres p false, hval p true, hval p false]
      linear_combination
        (-(coinWt W p
            * (W j p true * F p true + W j p false * F p false)))
          * hsum j p

end Tower

section Expect

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ) (ε : ℝ)

/-- Expanding a race-space sum into iterated coordinate sums. -/
theorem sum_RΩ_expand (f : RΩ A BL BR CC κ → ℝ) :
    ∑ ω : RΩ A BL BR CC κ, f ω
      = ∑ a : A.Ω, ∑ l : BL.Ω, ∑ r : BR.Ω, ∑ cc : CC.Ω,
          ∑ c : Fin κ → Bool, f (a, l, r, cc, c) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Fintype.sum_prod_type]

theorem sum_P_mul {ι : Type*} [Fintype ι] (P : ι → ℝ)
    (hs : ∑ i, P i = 1) (K : ℝ) (f : ι → ℝ)
    (hf : ∀ i, f i = K * P i) : ∑ i, f i = K := by
  rw [Finset.sum_congr rfl fun i _ => hf i, ← Finset.mul_sum, hs, mul_one]

/-- Marginalization: a function of the non-coin coordinates integrates
against the product of the side weights. -/
theorem RP_marg (hε : 0 < ε) (h : A.Ω → BL.Ω → BR.Ω → CC.Ω → ℝ) :
    ∑ ω : RΩ A BL BR CC κ,
        RP A BL BR CC κ ε ω * h ω.1 ω.2.1 ω.2.2.1 ω.2.2.2.1
      = ∑ a : A.Ω, ∑ l : BL.Ω, ∑ r : BR.Ω, ∑ cc : CC.Ω,
          A.P a * BL.P l * BR.P r * CC.P cc * h a l r cc := by
  rw [sum_RΩ_expand]
  refine Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun r _ =>
        Finset.sum_congr rfl fun cc _ => ?_
  have hcsum : ∑ c : Fin κ → Bool,
      coinWt (coinW A BL BR a l r (ε := ε)) c = 1 := by
    refine sum_coinWt fun j p => ?_
    show probL _ _ ε + probL _ _ ε = 1
    exact probL_add_probR _ _ ε hε
  calc ∑ c : Fin κ → Bool,
        RP A BL BR CC κ ε (a, l, r, cc, c) * h a l r cc
      = (A.P a * BL.P l * BR.P r * CC.P cc * h a l r cc)
          * ∑ c : Fin κ → Bool,
              coinWt (coinW A BL BR a l r (ε := ε)) c := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        show RP A BL BR CC κ ε (a, l, r, cc, c) * h a l r cc = _
        unfold RP
        show A.P a * (BL.P l * (BR.P r * (CC.P cc
          * coinWt (coinW A BL BR a l r (ε := ε)) c))) * h a l r cc = _
        ring
    _ = A.P a * BL.P l * BR.P r * CC.P cc * h a l r cc := by
        rw [hcsum, mul_one]

/-- Marginalization onto the head system. -/
theorem RP_margA (hε : 0 < ε) (g : A.Ω → ℝ) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω * g ω.1
      = ∑ a : A.Ω, A.P a * g a := by
  rw [RP_marg A BL BR CC κ ε hε (fun a _ _ _ => g a)]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine sum_P_mul BL.P BL.hPsum (A.P a * g a) _ fun l => ?_
  refine sum_P_mul BR.P BR.hPsum (A.P a * g a * BL.P l) _ fun r => ?_
  exact sum_P_mul CC.P CC.hPsum (A.P a * g a * BL.P l * BR.P r) _
    fun cc => by ring

/-- Marginalization onto the two side systems. -/
theorem RP_margLR (hε : 0 < ε) (g : BL.Ω → BR.Ω → ℝ) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω * g ω.2.1 ω.2.2.1
      = ∑ l : BL.Ω, ∑ r : BR.Ω, BL.P l * BR.P r * g l r := by
  rw [RP_marg A BL BR CC κ ε hε (fun _ l r _ => g l r)]
  refine sum_P_mul A.P A.hPsum
    (∑ l : BL.Ω, ∑ r : BR.Ω, BL.P l * BR.P r * g l r) _ fun a => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  exact sum_P_mul CC.P CC.hPsum (BL.P l * BR.P r * g l r * A.P a) _
    fun cc => by ring

/-- Marginalization onto the closing system. -/
theorem RP_margC (hε : 0 < ε) (g : CC.Ω → ℝ) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω * g ω.2.2.2.1
      = ∑ cc : CC.Ω, CC.P cc * g cc := by
  rw [RP_marg A BL BR CC κ ε hε (fun _ _ _ cc => g cc)]
  refine sum_P_mul A.P A.hPsum (∑ cc : CC.Ω, CC.P cc * g cc) _ fun a => ?_
  refine sum_P_mul BL.P BL.hPsum
    ((∑ cc : CC.Ω, CC.P cc * g cc) * A.P a) _ fun l => ?_
  refine sum_P_mul BR.P BR.hPsum
    ((∑ cc : CC.Ω, CC.P cc * g cc) * A.P a * BL.P l) _ fun r => ?_
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun cc _ => by ring

/-- The single-step tower property at the race level: the coin at step `j`
integrates against its conditional weights. -/
theorem race_tower (hε : 0 < ε) {j : ℕ} (hj : j < κ) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω *
        (if ω.2.2.2.2 ⟨j, hj⟩ = true then nextL A BL BR CC κ ω j
         else nextR A BL BR CC κ ω j)
      = ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω *
          (probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
              * nextL A BL BR CC κ ω j
            + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
              * nextR A BL BR CC κ ω j) := by
  rw [sum_RΩ_expand, sum_RΩ_expand]
  refine Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun r _ =>
        Finset.sum_congr rfl fun cc _ => ?_
  have hsum : ∀ (j' : ℕ) (p : Fin j' → Bool),
      coinW A BL BR a l r (ε := ε) j' p true
        + coinW A BL BR a l r (ε := ε) j' p false = 1 := by
    intro j' p
    show probL _ _ ε + probL _ _ ε = 1
    exact probL_add_probR _ _ ε hε
  show ∑ c : Fin κ → Bool,
      RP A BL BR CC κ ε (a, l, r, cc, c)
        * (if c ⟨j, hj⟩ = true then BL.sizeN (cntL c j) l
           else BR.sizeN (cntR c j) r)
    = ∑ c : Fin κ → Bool,
        RP A BL BR CC κ ε (a, l, r, cc, c)
          * (probL (BL.sizeN (cntL c j) l) (BR.sizeN (cntR c j) r) ε
              * BL.sizeN (cntL c j) l
            + probL (BR.sizeN (cntR c j) r) (BL.sizeN (cntL c j) l) ε
              * BR.sizeN (cntR c j) r)
  have hK : ∀ G : (Fin κ → Bool) → ℝ,
      (∑ c : Fin κ → Bool, RP A BL BR CC κ ε (a, l, r, cc, c) * G c)
        = A.P a * (BL.P l * (BR.P r * CC.P cc))
            * ∑ c : Fin κ → Bool,
                coinWt (coinW A BL BR a l r (ε := ε)) c * G c := by
    intro G
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    show A.P a * (BL.P l * (BR.P r * (CC.P cc
      * coinWt (coinW A BL BR a l r (ε := ε)) c))) * G c = _
    ring
  rw [hK, hK]
  congr 1
  calc ∑ c : Fin κ → Bool,
        coinWt (coinW A BL BR a l r (ε := ε)) c
          * (if c ⟨j, hj⟩ = true then BL.sizeN (cntL c j) l
             else BR.sizeN (cntR c j) r)
      = ∑ c : Fin κ → Bool,
          coinWt (coinW A BL BR a l r (ε := ε)) c
            * (if c ⟨j, hj⟩ = true
               then BL.sizeN (cntL (restrict c j (le_of_lt hj)) j) l
               else BR.sizeN (cntR (restrict c j (le_of_lt hj)) j) r) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [cntL_restrict c (le_of_lt hj) (le_refl j),
          cntR_restrict c (le_of_lt hj) (le_refl j)]
    _ = ∑ c : Fin κ → Bool,
          coinWt (coinW A BL BR a l r (ε := ε)) c
            * (coinW A BL BR a l r (ε := ε) j
                  (restrict c j (le_of_lt hj)) true
                * BL.sizeN (cntL (restrict c j (le_of_lt hj)) j) l
              + coinW A BL BR a l r (ε := ε) j
                  (restrict c j (le_of_lt hj)) false
                * BR.sizeN (cntR (restrict c j (le_of_lt hj)) j) r) :=
        coinWt_tower
          (fun p b => if b = true then BL.sizeN (cntL p j) l
            else BR.sizeN (cntR p j) r)
          (coinW A BL BR a l r (ε := ε)) hsum hj
    _ = ∑ c : Fin κ → Bool,
          coinWt (coinW A BL BR a l r (ε := ε)) c
            * (probL (BL.sizeN (cntL c j) l) (BR.sizeN (cntR c j) r) ε
                * BL.sizeN (cntL c j) l
              + probL (BR.sizeN (cntR c j) r) (BL.sizeN (cntL c j) l) ε
                * BR.sizeN (cntR c j) r) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        show coinWt (coinW A BL BR a l r (ε := ε)) c
            * (probL (BL.sizeN (cntL (restrict c j (le_of_lt hj)) j) l)
                  (BR.sizeN (cntR (restrict c j (le_of_lt hj)) j) r) ε
                * BL.sizeN (cntL (restrict c j (le_of_lt hj)) j) l
              + probL (BR.sizeN (cntR (restrict c j (le_of_lt hj)) j) r)
                  (BL.sizeN (cntL (restrict c j (le_of_lt hj)) j) l) ε
                * BR.sizeN (cntR (restrict c j (le_of_lt hj)) j) r) = _
        rw [cntL_restrict c (le_of_lt hj) (le_refl j),
          cntR_restrict c (le_of_lt hj) (le_refl j)]

/-- The expected consumed mass equals the expected sum of the conditional
consumption rates. -/
theorem sum_consumed (hε : 0 < ε) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (sumL A BL BR CC κ ω + sumR A BL BR CC κ ω)
      = ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * ∑ j ∈ Finset.range κ,
              (probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
                  * nextL A BL BR CC κ ω j
                + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
                  * nextR A BL BR CC κ ω j) := by
  have hpath : ∀ ω : RΩ A BL BR CC κ,
      sumL A BL BR CC κ ω + sumR A BL BR CC κ ω
        = ∑ j : Fin κ, (if ω.2.2.2.2 j = true
            then nextL A BL BR CC κ ω (j : ℕ)
            else nextR A BL BR CC κ ω (j : ℕ)) := by
    intro ω
    unfold sumL sumR
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hb : ω.2.2.2.2 i = true
    · rw [if_pos hb, if_pos hb, if_pos hb, add_zero]
    · rw [if_neg hb, if_neg hb, if_neg hb, zero_add]
  calc ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (sumL A BL BR CC κ ω + sumR A BL BR CC κ ω)
      = ∑ ω : RΩ A BL BR CC κ, ∑ j : Fin κ,
          RP A BL BR CC κ ε ω * (if ω.2.2.2.2 j = true
            then nextL A BL BR CC κ ω (j : ℕ)
            else nextR A BL BR CC κ ω (j : ℕ)) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [hpath ω, Finset.mul_sum]
    _ = ∑ j : Fin κ, ∑ ω : RΩ A BL BR CC κ,
          RP A BL BR CC κ ε ω * (if ω.2.2.2.2 j = true
            then nextL A BL BR CC κ ω (j : ℕ)
            else nextR A BL BR CC κ ω (j : ℕ)) := Finset.sum_comm
    _ = ∑ j : Fin κ, ∑ ω : RΩ A BL BR CC κ,
          RP A BL BR CC κ ε ω
            * (probL (nextL A BL BR CC κ ω (j : ℕ))
                  (nextR A BL BR CC κ ω (j : ℕ)) ε
                * nextL A BL BR CC κ ω (j : ℕ)
              + probL (nextR A BL BR CC κ ω (j : ℕ))
                  (nextL A BL BR CC κ ω (j : ℕ)) ε
                * nextR A BL BR CC κ ω (j : ℕ)) := by
        refine Finset.sum_congr rfl fun jf _ => ?_
        exact race_tower A BL BR CC κ ε hε jf.isLt
    _ = ∑ ω : RΩ A BL BR CC κ, ∑ j : Fin κ,
          RP A BL BR CC κ ε ω
            * (probL (nextL A BL BR CC κ ω (j : ℕ))
                  (nextR A BL BR CC κ ω (j : ℕ)) ε
                * nextL A BL BR CC κ ω (j : ℕ)
              + probL (nextR A BL BR CC κ ω (j : ℕ))
                  (nextL A BL BR CC κ ω (j : ℕ)) ε
                * nextR A BL BR CC κ ω (j : ℕ)) := Finset.sum_comm
    _ = ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * ∑ j ∈ Finset.range κ,
              (probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
                  * nextL A BL BR CC κ ω j
                + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
                  * nextR A BL BR CC κ ω j) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [← Finset.mul_sum,
          Fin.sum_univ_eq_sum_range
            (fun n => probL (nextL A BL BR CC κ ω n)
                (nextR A BL BR CC κ ω n) ε * nextL A BL BR CC κ ω n
              + probL (nextR A BL BR CC κ ω n)
                  (nextL A BL BR CC κ ω n) ε * nextR A BL BR CC κ ω n) κ]

/-- Expectation linearity helpers. -/
theorem sum_mul_sub {ι : Type*} [Fintype ι] (P f g : ι → ℝ) :
    ∑ i, P i * (f i - g i) = (∑ i, P i * f i) - ∑ i, P i * g i := by
  rw [Finset.sum_congr rfl (fun i _ =>
    show P i * (f i - g i) = P i * f i - P i * g i from by ring),
    Finset.sum_sub_distrib]

theorem sum_mul_sub_sub {ι : Type*} [Fintype ι] (P f g : ι → ℝ) (c : ℝ)
    (hs : ∑ i, P i = 1) :
    ∑ i, P i * (f i - g i - c)
      = (∑ i, P i * f i) - (∑ i, P i * g i) - c := by
  rw [Finset.sum_congr rfl (fun i _ =>
    show P i * (f i - g i - c) = P i * f i - P i * g i - P i * c from
      by ring),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    sum_P_mul P hs c (fun i => P i * c) (fun i => by ring)]

theorem sum_mul_div_sub {ι : Type*} [Fintype ι] (P f : ι → ℝ) (c : ℝ)
    (hs : ∑ i, P i = 1) :
    ∑ i, P i * (f i / 2 - c) = (∑ i, P i * f i) / 2 - c := by
  rw [Finset.sum_congr rfl (fun i _ =>
    show P i * (f i / 2 - c) = P i * f i / 2 - P i * c from by ring),
    Finset.sum_sub_distrib, ← Finset.sum_div,
    sum_P_mul P hs c (fun i => P i * c) (fun i => by ring)]

theorem sum_mul_min {ι : Type*} [Fintype ι] (P f g : ι → ℝ) :
    ∑ i, P i * min (f i) (g i)
      = (∑ i, P i * (f i + g i)) / 2 - (∑ i, P i * |f i - g i|) / 2 := by
  rw [Finset.sum_congr rfl (fun i _ =>
    show P i * min (f i) (g i)
        = P i * (f i + g i) / 2 - P i * |f i - g i| / 2 from by
      rw [min_eq_avg]
      ring),
    Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]

/-- The expected shortfall below the target is controlled by the standard
deviation (Cauchy–Schwarz). -/
theorem pos_part_le {ι : Type*} [Fintype ι] (P X : ι → ℝ) {T' V : ℝ}
    (hP : ∀ i, 0 ≤ P i) (hs : ∑ i, P i = 1) (hV0 : 0 ≤ V)
    (hT : T' ≤ ∑ i, P i * X i)
    (hV : ∑ i, P i * (X i - ∑ i', P i' * X i') ^ 2 ≤ V) :
    ∑ i, P i * max (T' - X i) 0 ≤ Real.sqrt V := by
  set m := ∑ i', P i' * X i' with hm
  have hpath : ∀ i, max (T' - X i) 0 ≤ |X i - m| := by
    intro i
    refine max_le ?_ (abs_nonneg _)
    have h1 : T' - X i ≤ m - X i := by linarith
    refine le_trans h1 ?_
    rw [abs_sub_comm]
    exact le_abs_self _
  have h1 : ∑ i, P i * max (T' - X i) 0 ≤ ∑ i, P i * |X i - m| :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hpath i) (hP i)
  refine le_trans h1 ?_
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (P i)) (fun i => Real.sqrt (P i) * |X i - m|)
  have he1 : ∀ i, Real.sqrt (P i) * (Real.sqrt (P i) * |X i - m|)
      = P i * |X i - m| := by
    intro i
    rw [← mul_assoc, Real.mul_self_sqrt (hP i)]
  have he2 : ∀ i, Real.sqrt (P i) ^ 2 = P i := fun i => Real.sq_sqrt (hP i)
  have he3 : ∀ i, (Real.sqrt (P i) * |X i - m|) ^ 2
      = P i * (X i - m) ^ 2 := by
    intro i
    rw [mul_pow, Real.sq_sqrt (hP i), sq_abs]
  rw [Finset.sum_congr rfl fun i _ => he1 i,
    Finset.sum_congr rfl fun i _ => he2 i,
    Finset.sum_congr rfl fun i _ => he3 i, hs, one_mul] at hcs
  have hnn : 0 ≤ ∑ i, P i * |X i - m| :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hP i) (abs_nonneg _)
  have h2 : (∑ i, P i * |X i - m|) ^ 2 ≤ V := le_trans hcs hV
  calc ∑ i, P i * |X i - m|
      = Real.sqrt ((∑ i, P i * |X i - m|) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt V := Real.sqrt_le_sqrt h2

/-- The expected minimum of two independent totals is close to the target
when both concentrate. -/
theorem min_indep_ge {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (P1 : ι₁ → ℝ) (P2 : ι₂ → ℝ) (X1 : ι₁ → ℝ) (X2 : ι₂ → ℝ) {T' V : ℝ}
    (hP1 : ∀ i, 0 ≤ P1 i) (hP2 : ∀ i, 0 ≤ P2 i)
    (hs1 : ∑ i, P1 i = 1) (hs2 : ∑ i, P2 i = 1) (hV0 : 0 ≤ V)
    (hT1 : T' ≤ ∑ i, P1 i * X1 i) (hT2 : T' ≤ ∑ i, P2 i * X2 i)
    (hV1 : ∑ i, P1 i * (X1 i - ∑ i', P1 i' * X1 i') ^ 2 ≤ V)
    (hV2 : ∑ i, P2 i * (X2 i - ∑ i', P2 i' * X2 i') ^ 2 ≤ V) :
    T' - 2 * Real.sqrt V
      ≤ ∑ i : ι₁, ∑ i2 : ι₂, P1 i * P2 i2 * min (X1 i) (X2 i2) := by
  have hmin : ∀ x y : ℝ,
      T' - max (T' - x) 0 - max (T' - y) 0 ≤ min x y := by
    intro x y
    rcases le_total x y with h | h
    · rw [min_eq_left h]
      linarith [le_max_left (T' - x) 0, le_max_right (T' - y) 0]
    · rw [min_eq_right h]
      linarith [le_max_left (T' - y) 0, le_max_right (T' - x) 0]
  have hstep : ∑ i : ι₁, ∑ i2 : ι₂,
      P1 i * P2 i2 * (T' - max (T' - X1 i) 0 - max (T' - X2 i2) 0)
      ≤ ∑ i : ι₁, ∑ i2 : ι₂, P1 i * P2 i2 * min (X1 i) (X2 i2) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun i2 _ => ?_
    exact mul_le_mul_of_nonneg_left (hmin (X1 i) (X2 i2))
      (mul_nonneg (hP1 i) (hP2 i2))
  refine le_trans ?_ hstep
  have h1 : ∀ i : ι₁, ∑ i2 : ι₂,
      P1 i * P2 i2 * (T' - max (T' - X1 i) 0 - max (T' - X2 i2) 0)
      = P1 i * T' - P1 i * max (T' - X1 i) 0
          - P1 i * ∑ i2 : ι₂, P2 i2 * max (T' - X2 i2) 0 := by
    intro i
    rw [Finset.sum_congr rfl (fun i2 _ =>
      show P1 i * P2 i2 * (T' - max (T' - X1 i) 0 - max (T' - X2 i2) 0)
          = (P1 i * T' - P1 i * max (T' - X1 i) 0) * P2 i2
            - P1 i * (P2 i2 * max (T' - X2 i2) 0) from by ring),
      Finset.sum_sub_distrib,
      sum_P_mul P2 hs2 (P1 i * T' - P1 i * max (T' - X1 i) 0)
        (fun i2 => (P1 i * T' - P1 i * max (T' - X1 i) 0) * P2 i2)
        (fun i2 => rfl),
      ← Finset.mul_sum]
  have hexp : ∑ i : ι₁, ∑ i2 : ι₂,
      P1 i * P2 i2 * (T' - max (T' - X1 i) 0 - max (T' - X2 i2) 0)
      = T' - (∑ i, P1 i * max (T' - X1 i) 0)
          - ∑ i2, P2 i2 * max (T' - X2 i2) 0 := by
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib,
      sum_P_mul P1 hs1 T' (fun i => P1 i * T') (fun i => by ring),
      ← Finset.sum_mul, hs1, one_mul]
  rw [hexp]
  linarith [pos_part_le P1 X1 hP1 hs1 hV0 hT1 hV1,
    pos_part_le P2 X2 hP2 hs2 hV0 hT2 hV2]

/-- The race total: the expected total size of the race system dominates
three targets minus sacrifices, clamps, and concentration slack, plus half
of the imbalance gain. -/
theorem race_total (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (hcB : 0 ≤ cB) {V G : ℝ} (hV0 : 0 ≤ V)
    (hVarL : ∑ l : BL.Ω, BL.P l * ((∑ i, BL.size l i)
        - ∑ l' : BL.Ω, BL.P l' * ∑ i, BL.size l' i) ^ 2 ≤ V)
    (hVarR : ∑ r : BR.Ω, BR.P r * ((∑ i, BR.size r i)
        - ∑ r' : BR.Ω, BR.P r' * ∑ i, BR.size r' i) ^ 2 ≤ V)
    (hG : G ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|) :
    3 * T + G / 2 - 2 * cB - (κ : ℝ) * ε / 2 - 2 * Real.sqrt V
      ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * ∑ i : Fin (mrace A BL BR CC κ),
              rsize A BL BR CC κ ε ω (i : ℕ) := by
  have hRPs : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω = 1 :=
    RP_sum A BL BR CC κ ε hε
  have hRP0 : ∀ ω : RΩ A BL BR CC κ, 0 ≤ RP A BL BR CC κ ε ω :=
    fun ω => (RP_pos A BL BR CC κ ε hε ω).le
  -- pathwise decomposition of the expected total
  have hdec : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * ∑ i : Fin (mrace A BL BR CC κ), rsize A BL BR CC κ ε ω (i : ℕ)
    = (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω * preSum A ω.1 A.m)
      + (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * ∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j)
      + (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * survPart A BL BR CC κ ω)
      + (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * ccPart A BL BR CC κ ω) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [rsum_decomp A BL BR CC κ ε hκL hκR ω]
    ring
  rw [hdec]
  -- the A part
  have hEA : T ≤ ∑ ω : RΩ A BL BR CC κ,
      RP A BL BR CC κ ε ω * preSum A ω.1 A.m := by
    have h1 : ∑ ω : RΩ A BL BR CC κ,
        RP A BL BR CC κ ε ω * preSum A ω.1 A.m
        = ∑ a : A.Ω, A.P a * preSum A a A.m :=
      RP_margA A BL BR CC κ ε hε (fun a => preSum A a A.m)
    rw [h1]
    refine le_trans A.htotal (le_of_eq ?_)
    exact Finset.sum_congr rfl fun a _ => by rw [preSum_total]
  -- the closing part
  have hEcc : T - cB ≤ ∑ ω : RΩ A BL BR CC κ,
      RP A BL BR CC κ ε ω * ccPart A BL BR CC κ ω := by
    have h1 : ∑ ω : RΩ A BL BR CC κ,
        RP A BL BR CC κ ε ω * ccPart A BL BR CC κ ω
        = ∑ cc : CC.Ω, CC.P cc
            * (preSum CC cc CC.m - preSum CC cc 1) :=
      RP_margC A BL BR CC κ ε hε
        (fun cc => preSum CC cc CC.m - preSum CC cc 1)
    rw [h1, sum_mul_sub]
    have h2 : T ≤ ∑ cc : CC.Ω, CC.P cc * preSum CC cc CC.m := by
      refine le_trans CC.htotal (le_of_eq ?_)
      exact Finset.sum_congr rfl fun cc _ => by rw [preSum_total]
    have h3 : ∑ cc : CC.Ω, CC.P cc * preSum CC cc 1 ≤ cB := by
      have h4 : ∀ cc : CC.Ω, CC.P cc * preSum CC cc 1
          ≤ CC.P cc * cB := by
        intro cc
        refine mul_le_mul_of_nonneg_left ?_ (CC.hP cc).le
        have h5 : preSum CC cc 1 = CC.sizeN 0 cc := by
          unfold preSum
          rw [Finset.sum_range_one]
        rw [h5]
        exact sizeN_le_cB CC hcB 0 cc
      refine le_trans (Finset.sum_le_sum fun cc _ => h4 cc) (le_of_eq ?_)
      exact sum_P_mul CC.P CC.hPsum cB (fun cc => CC.P cc * cB)
        (fun cc => by ring)
    linarith
  -- the survivor part against the independent minimum
  have hEm1 : T - 2 * Real.sqrt V ≤ ∑ ω : RΩ A BL BR CC κ,
      RP A BL BR CC κ ε ω
        * min (preSum BL ω.2.1 BL.m) (preSum BR ω.2.2.1 BR.m) := by
    have h1 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * min (preSum BL ω.2.1 BL.m) (preSum BR ω.2.2.1 BR.m)
        = ∑ l : BL.Ω, ∑ r : BR.Ω, BL.P l * BR.P r
            * min (preSum BL l BL.m) (preSum BR r BR.m) :=
      RP_margLR A BL BR CC κ ε hε
        (fun l r => min (preSum BL l BL.m) (preSum BR r BR.m))
    rw [h1]
    have hmeanL : ∑ l' : BL.Ω, BL.P l' * preSum BL l' BL.m
        = ∑ l' : BL.Ω, BL.P l' * ∑ i, BL.size l' i :=
      Finset.sum_congr rfl fun l' _ => by rw [preSum_total]
    have hmeanR : ∑ r' : BR.Ω, BR.P r' * preSum BR r' BR.m
        = ∑ r' : BR.Ω, BR.P r' * ∑ i, BR.size r' i :=
      Finset.sum_congr rfl fun r' _ => by rw [preSum_total]
    have hTL : T ≤ ∑ l : BL.Ω, BL.P l * preSum BL l BL.m := by
      refine le_trans BL.htotal (le_of_eq ?_)
      exact Finset.sum_congr rfl fun l _ => by rw [preSum_total]
    have hTR : T ≤ ∑ r : BR.Ω, BR.P r * preSum BR r BR.m := by
      refine le_trans BR.htotal (le_of_eq ?_)
      exact Finset.sum_congr rfl fun r _ => by rw [preSum_total]
    have hVL : ∑ l : BL.Ω, BL.P l * (preSum BL l BL.m
        - ∑ l' : BL.Ω, BL.P l' * preSum BL l' BL.m) ^ 2 ≤ V := by
      refine le_trans (le_of_eq ?_) hVarL
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [preSum_total, hmeanL]
    have hVR : ∑ r : BR.Ω, BR.P r * (preSum BR r BR.m
        - ∑ r' : BR.Ω, BR.P r' * preSum BR r' BR.m) ^ 2 ≤ V := by
      refine le_trans (le_of_eq ?_) hVarR
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [preSum_total, hmeanR]
    exact min_indep_ge BL.P BR.P (fun l => preSum BL l BL.m)
      (fun r => preSum BR r BR.m) (fun l => (BL.hP l).le)
      (fun r => (BR.hP r).le) BL.hPsum BR.hPsum hV0 hTL hTR hVL hVR
  have hEsurv : (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * min (preSum BL ω.2.1 BL.m) (preSum BR ω.2.2.1 BR.m))
      - (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * min (sumL A BL BR CC κ ω) (sumR A BL BR CC κ ω)) - cB
      ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * survPart A BL BR CC κ ω := by
    have h1 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (min (preSum BL ω.2.1 BL.m) (preSum BR ω.2.2.1 BR.m)
            - min (sumL A BL BR CC κ ω) (sumR A BL BR CC κ ω) - cB)
        ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * survPart A BL BR CC κ ω :=
      Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
        (survPart_ge A BL BR CC κ hcB ω) (hRP0 ω)
    refine le_trans (le_of_eq ?_) h1
    exact (sum_mul_sub_sub (RP A BL BR CC κ ε)
      (fun ω => min (preSum BL ω.2.1 BL.m) (preSum BR ω.2.2.1 BR.m))
      (fun ω => min (sumL A BL BR CC κ ω) (sumR A BL BR CC κ ω))
      cB hRPs).symm
  -- the consumed minimum in terms of the gain
  have hEm2 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * min (sumL A BL BR CC κ ω) (sumR A BL BR CC κ ω)
      = (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * (sumL A BL BR CC κ ω + sumR A BL BR CC κ ω)) / 2
        - (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|) / 2 :=
    sum_mul_min (RP A BL BR CC κ ε) (fun ω => sumL A BL BR CC κ ω)
      (fun ω => sumR A BL BR CC κ ω)
  -- the coin part against half the expected consumption
  have hEcoin : (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (sumL A BL BR CC κ ω + sumR A BL BR CC κ ω)) / 2
        - (κ : ℝ) * ε / 2
      ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * ∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j := by
    have hcoinpath : ∀ ω : RΩ A BL BR CC κ,
        (∑ j ∈ Finset.range κ,
            (probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
                * nextL A BL BR CC κ ω j
              + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
                * nextR A BL BR CC κ ω j)) / 2 - (κ : ℝ) * ε / 2
          ≤ ∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j := by
      intro ω
      have h1 : ∀ j ∈ Finset.range κ,
          (probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
              * nextL A BL BR CC κ ω j
            + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
              * nextR A BL BR CC κ ω j) / 2 - ε / 2
            ≤ coinTerm A BL BR CC κ ε ω j :=
        fun j _ => coinTerm_ge A BL BR CC κ ε hε ω j
      refine le_trans (le_of_eq ?_) (Finset.sum_le_sum h1)
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      ring
    have h2 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * ((∑ j ∈ Finset.range κ,
            (probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
                * nextL A BL BR CC κ ω j
              + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
                * nextR A BL BR CC κ ω j)) / 2 - (κ : ℝ) * ε / 2)
        ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * ∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j :=
      Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
        (hcoinpath ω) (hRP0 ω)
    refine le_trans (le_of_eq ?_) h2
    rw [sum_mul_div_sub (RP A BL BR CC κ ε)
      (fun ω => ∑ j ∈ Finset.range κ,
        (probL (nextL A BL BR CC κ ω j) (nextR A BL BR CC κ ω j) ε
            * nextL A BL BR CC κ ω j
          + probL (nextR A BL BR CC κ ω j) (nextL A BL BR CC κ ω j) ε
            * nextR A BL BR CC κ ω j))
      ((κ : ℝ) * ε / 2) hRPs, ← sum_consumed A BL BR CC κ ε hε]
  linarith

/-- The race variance: crude three-block bound. The head and closing
blocks contribute their carried variances; the middle (side/coin) block is
bounded by its range. -/
theorem race_var (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    (hcB : 0 ≤ cB) {V : ℝ}
    (hVarA : ∑ a : A.Ω, A.P a * ((∑ i, A.size a i)
        - ∑ a' : A.Ω, A.P a' * ∑ i, A.size a' i) ^ 2 ≤ V)
    (hVarC : ∑ cc : CC.Ω, CC.P cc * ((∑ i, CC.size cc i)
        - ∑ cc' : CC.Ω, CC.P cc' * ∑ i, CC.size cc' i) ^ 2 ≤ V) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * ((∑ i : Fin (mrace A BL BR CC κ),
              rsize A BL BR CC κ ε ω (i : ℕ))
          - ∑ ω' : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω'
              * ∑ i : Fin (mrace A BL BR CC κ),
                  rsize A BL BR CC κ ε ω' (i : ℕ)) ^ 2
      ≤ 9 * V + 6 * cB ^ 2
        + 3 * (2 * ((BL.m : ℝ) + (BR.m : ℝ)) * cB) ^ 2 := by
  have hRPs : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω = 1 :=
    RP_sum A BL BR CC κ ε hε
  have hRP0 : ∀ ω : RΩ A BL BR CC κ, 0 ≤ RP A BL BR CC κ ε ω :=
    fun ω => (RP_pos A BL BR CC κ ε hε ω).le
  set m1 := ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
    * preSum A ω.1 A.m with hm1
  set m2 := ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
    * (∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j
        + survPart A BL BR CC κ ω) with hm2
  set m3 := ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
    * ccPart A BL BR CC κ ω with hm3
  set B := 2 * ((BL.m : ℝ) + (BR.m : ℝ)) * cB with hB
  have hmean : ∑ ω' : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω'
      * ∑ i : Fin (mrace A BL BR CC κ), rsize A BL BR CC κ ε ω' (i : ℕ)
      = m1 + m2 + m3 := by
    rw [hm1, hm2, hm3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [rsum_decomp A BL BR CC κ ε hκL hκR ω]
    ring
  rw [hmean]
  have hpath : ∀ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * ((∑ i : Fin (mrace A BL BR CC κ),
            rsize A BL BR CC κ ε ω (i : ℕ)) - (m1 + m2 + m3)) ^ 2
      ≤ RP A BL BR CC κ ε ω
          * (3 * (preSum A ω.1 A.m - m1) ^ 2
            + 3 * ((∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j
                + survPart A BL BR CC κ ω) - m2) ^ 2
            + 3 * (ccPart A BL BR CC κ ω - m3) ^ 2) := by
    intro ω
    refine mul_le_mul_of_nonneg_left ?_ (hRP0 ω)
    rw [rsum_decomp A BL BR CC κ ε hκL hκR ω]
    nlinarith [sq_nonneg ((preSum A ω.1 A.m - m1)
        - ((∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j
            + survPart A BL BR CC κ ω) - m2)),
      sq_nonneg ((preSum A ω.1 A.m - m1)
        - (ccPart A BL BR CC κ ω - m3)),
      sq_nonneg (((∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j
            + survPart A BL BR CC κ ω) - m2)
        - (ccPart A BL BR CC κ ω - m3))]
  refine le_trans (Finset.sum_le_sum fun ω _ => hpath ω) ?_
  have hdist : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (3 * (preSum A ω.1 A.m - m1) ^ 2
        + 3 * ((∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j
            + survPart A BL BR CC κ ω) - m2) ^ 2
        + 3 * (ccPart A BL BR CC κ ω - m3) ^ 2)
      = 3 * (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * (preSum A ω.1 A.m - m1) ^ 2)
        + 3 * (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * ((∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j
                + survPart A BL BR CC κ ω) - m2) ^ 2)
        + 3 * (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * (ccPart A BL BR CC κ ω - m3) ^ 2) := by
    rw [Finset.sum_congr rfl (fun ω _ =>
      show RP A BL BR CC κ ε ω
          * (3 * (preSum A ω.1 A.m - m1) ^ 2
            + 3 * ((∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j
                + survPart A BL BR CC κ ω) - m2) ^ 2
            + 3 * (ccPart A BL BR CC κ ω - m3) ^ 2)
        = 3 * (RP A BL BR CC κ ε ω * (preSum A ω.1 A.m - m1) ^ 2)
          + (3 * (RP A BL BR CC κ ε ω
              * ((∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j
                  + survPart A BL BR CC κ ω) - m2) ^ 2)
            + 3 * (RP A BL BR CC κ ε ω
                * (ccPart A BL BR CC κ ω - m3) ^ 2)) from by ring),
      Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [hdist]
  -- head block: carried variance
  have hEA' : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (preSum A ω.1 A.m - m1) ^ 2 ≤ V := by
    have h1 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (preSum A ω.1 A.m - m1) ^ 2
        = ∑ a : A.Ω, A.P a * (preSum A a A.m - m1) ^ 2 :=
      RP_margA A BL BR CC κ ε hε (fun a => (preSum A a A.m - m1) ^ 2)
    have hmeanA : ∑ a' : A.Ω, A.P a' * preSum A a' A.m
        = ∑ a' : A.Ω, A.P a' * ∑ i, A.size a' i :=
      Finset.sum_congr rfl fun a' _ => by rw [preSum_total]
    have h2 : m1 = ∑ a' : A.Ω, A.P a' * preSum A a' A.m := by
      rw [hm1]
      exact RP_margA A BL BR CC κ ε hε (fun a => preSum A a A.m)
    rw [h1]
    refine le_trans (le_of_eq ?_) hVarA
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [preSum_total, h2, hmeanA]
  -- middle block: range bound
  have hcoinB : ∀ ω : RΩ A BL BR CC κ,
      ∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j
        ≤ (κ : ℝ) * cB := by
    intro ω
    refine le_trans (Finset.sum_le_sum fun j _ =>
      coinTerm_le_cB A BL BR CC κ ε hε hcB ω j) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hg0 : ∀ ω : RΩ A BL BR CC κ,
      0 ≤ ∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j
        + survPart A BL BR CC κ ω := by
    intro ω
    have h1 := Finset.sum_nonneg fun j (_ : j ∈ Finset.range κ) =>
      coinTerm_nonneg A BL BR CC κ ε hε ω j
    linarith [survPart_nonneg A BL BR CC κ ω]
  have hgB : ∀ ω : RΩ A BL BR CC κ,
      ∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j
        + survPart A BL BR CC κ ω ≤ B := by
    intro ω
    have h1 := hcoinB ω
    have h2 := survPart_le A BL BR CC κ hcB ω
    push_cast at h2
    have h3 : (κ : ℝ) * cB ≤ (BL.m : ℝ) * cB :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hκL) hcB
    have h4 : max (BL.m : ℝ) (BR.m : ℝ) * cB
        ≤ ((BL.m : ℝ) + (BR.m : ℝ)) * cB := by
      refine mul_le_mul_of_nonneg_right (max_le ?_ ?_) hcB
      · linarith [Nat.cast_nonneg (α := ℝ) BR.m]
      · linarith [Nat.cast_nonneg (α := ℝ) BL.m]
    have h5 : (BL.m : ℝ) * cB ≤ ((BL.m : ℝ) + (BR.m : ℝ)) * cB :=
      mul_le_mul_of_nonneg_right
        (by linarith [Nat.cast_nonneg (α := ℝ) BR.m]) hcB
    rw [hB]
    linarith
  have hm20 : 0 ≤ m2 := by
    rw [hm2]
    exact Finset.sum_nonneg fun ω _ => mul_nonneg (hRP0 ω) (hg0 ω)
  have hm2B : m2 ≤ B := by
    rw [hm2]
    refine le_trans (Finset.sum_le_sum fun ω _ =>
      mul_le_mul_of_nonneg_left (hgB ω) (hRP0 ω)) (le_of_eq ?_)
    exact sum_P_mul (RP A BL BR CC κ ε) hRPs B
      (fun ω => RP A BL BR CC κ ε ω * B) (fun ω => by ring)
  have hEG' : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * ((∑ j ∈ Finset.range κ, coinTerm A BL BR CC κ ε ω j
          + survPart A BL BR CC κ ω) - m2) ^ 2 ≤ B ^ 2 := by
    refine le_trans (Finset.sum_le_sum fun ω _ =>
      mul_le_mul_of_nonneg_left
        (sq_le_sq' (b := B) (by linarith [hg0 ω, hm2B])
          (by linarith [hgB ω, hm20]))
        (hRP0 ω)) (le_of_eq ?_)
    exact sum_P_mul (RP A BL BR CC κ ε) hRPs (B ^ 2)
      (fun ω => RP A BL BR CC κ ε ω * B ^ 2) (fun ω => by ring)
  -- closing block: carried variance plus one clamped chunk
  have hEC' : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (ccPart A BL BR CC κ ω - m3) ^ 2 ≤ 2 * V + 2 * cB ^ 2 := by
    have h1 : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * (ccPart A BL BR CC κ ω - m3) ^ 2
        = ∑ cc : CC.Ω, CC.P cc
            * ((preSum CC cc CC.m - preSum CC cc 1) - m3) ^ 2 :=
      RP_margC A BL BR CC κ ε hε
        (fun cc => ((preSum CC cc CC.m - preSum CC cc 1) - m3) ^ 2)
    have h2a : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * ccPart A BL BR CC κ ω
        = ∑ cc : CC.Ω, CC.P cc
            * (preSum CC cc CC.m - preSum CC cc 1) :=
      RP_margC A BL BR CC κ ε hε
        (fun cc => preSum CC cc CC.m - preSum CC cc 1)
    have h2 : m3 = (∑ cc : CC.Ω, CC.P cc * preSum CC cc CC.m)
        - ∑ cc : CC.Ω, CC.P cc * preSum CC cc 1 := by
      rw [hm3, h2a, sum_mul_sub]
    have hp0 : ∀ cc : CC.Ω, 0 ≤ preSum CC cc 1 :=
      fun cc => preSum_nonneg CC cc 1
    have hpB : ∀ cc : CC.Ω, preSum CC cc 1 ≤ cB := by
      intro cc
      have h5 : preSum CC cc 1 = CC.sizeN 0 cc := by
        unfold preSum
        rw [Finset.sum_range_one]
      rw [h5]
      exact sizeN_le_cB CC hcB 0 cc
    have hμ0 : 0 ≤ ∑ cc : CC.Ω, CC.P cc * preSum CC cc 1 :=
      Finset.sum_nonneg fun cc _ => mul_nonneg (CC.hP cc).le (hp0 cc)
    have hμB : ∑ cc : CC.Ω, CC.P cc * preSum CC cc 1 ≤ cB := by
      refine le_trans (Finset.sum_le_sum fun cc _ =>
        mul_le_mul_of_nonneg_left (hpB cc) (CC.hP cc).le) (le_of_eq ?_)
      exact sum_P_mul CC.P CC.hPsum cB (fun cc => CC.P cc * cB)
        (fun cc => by ring)
    have hb1 : ∀ cc : CC.Ω,
        ((preSum CC cc CC.m - preSum CC cc 1) - m3) ^ 2
          ≤ 2 * (preSum CC cc CC.m
              - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m) ^ 2
            + 2 * (preSum CC cc 1
              - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1) ^ 2 := by
      intro cc
      rw [h2]
      nlinarith [sq_nonneg ((preSum CC cc CC.m
          - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m)
        + (preSum CC cc 1
          - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1))]
    rw [h1]
    refine le_trans (Finset.sum_le_sum fun cc _ =>
      mul_le_mul_of_nonneg_left (hb1 cc) (CC.hP cc).le) ?_
    have hsplit2 : ∑ cc : CC.Ω, CC.P cc
        * (2 * (preSum CC cc CC.m
            - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m) ^ 2
          + 2 * (preSum CC cc 1
            - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1) ^ 2)
        = 2 * (∑ cc : CC.Ω, CC.P cc * (preSum CC cc CC.m
            - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m) ^ 2)
          + 2 * (∑ cc : CC.Ω, CC.P cc * (preSum CC cc 1
            - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1) ^ 2) := by
      rw [Finset.sum_congr rfl (fun cc _ =>
        show CC.P cc
            * (2 * (preSum CC cc CC.m
                - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m) ^ 2
              + 2 * (preSum CC cc 1
                - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1) ^ 2)
          = 2 * (CC.P cc * (preSum CC cc CC.m
              - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m) ^ 2)
            + 2 * (CC.P cc * (preSum CC cc 1
              - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1) ^ 2)
          from by ring),
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hsplit2]
    have hmeanC : ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m
        = ∑ cc' : CC.Ω, CC.P cc' * ∑ i, CC.size cc' i :=
      Finset.sum_congr rfl fun cc' _ => by rw [preSum_total]
    have hVt : ∑ cc : CC.Ω, CC.P cc * (preSum CC cc CC.m
        - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' CC.m) ^ 2 ≤ V := by
      refine le_trans (le_of_eq ?_) hVarC
      refine Finset.sum_congr rfl fun cc _ => ?_
      rw [preSum_total, hmeanC]
    have hVp : ∑ cc : CC.Ω, CC.P cc * (preSum CC cc 1
        - ∑ cc' : CC.Ω, CC.P cc' * preSum CC cc' 1) ^ 2 ≤ cB ^ 2 := by
      refine le_trans (Finset.sum_le_sum fun cc _ =>
        mul_le_mul_of_nonneg_left
          (sq_le_sq' (b := cB) (by linarith [hp0 cc, hμB])
            (by linarith [hpB cc, hμ0]))
          (CC.hP cc).le) (le_of_eq ?_)
      exact sum_P_mul CC.P CC.hPsum (cB ^ 2)
        (fun cc => CC.P cc * cB ^ 2) (fun cc => by ring)
    linarith
  linarith

end Expect

end Race

end KServer


