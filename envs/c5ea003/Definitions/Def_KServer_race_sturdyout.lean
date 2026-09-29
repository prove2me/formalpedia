-- Prove2me | Definitions.Def_KServer_race_sturdyout
-- name    : KServer_race_sturdyout
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T22:35:15.838882+00:00
-- url     : https://prove2.me/theorems/c3c092b4-f088-444c-9988-649e67c8a9fd
-- title:
--   Race output invariants at head-phase depths
-- statement:
--   At depths n at most A.m, the race filtration atom is exactly the head system's atom, and the remaining phases are independent of it. Consequently the L1 drawdown of the race total at such depths equals the head system's L1 drawdown (race_drawdown_A, an equality), and the expected below-floor chunk count among the first n' at most A.m race chunks equals the head system's (race_badcount_A). Includes restricted marginalizations of the race measure over head events.
-- source:
--   Bansal-Cohen-Ravi style randomized k-server lower bound

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
import Definitions.Def_KServer_race_sel

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 3200000

namespace KServer

namespace Race

variable {X : Type*} [MetricSpace X]
variable {s t : X} {cB T pe : ℝ} {mL : ℕ}

section SturdyOut

variable (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
variable (κ : ℕ) (ε : ℝ)

/-- The race atoms at head-phase depths are the head atoms. -/
theorem race_atom_A {n : ℕ} (hn : n ≤ A.m) (ω : RΩ A BL BR CC κ) :
    Finset.univ.filter (fun ω' : RΩ A BL BR CC κ =>
        rhist2 A BL BR CC κ ω' n = rhist2 A BL BR CC κ ω n)
      = Finset.univ.filter (fun ω' : RΩ A BL BR CC κ =>
          A.hist n ω'.1 = A.hist n ω.1) := by
  ext ω'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [rhist2_le_A A BL BR CC κ ω' hn, rhist2_le_A A BL BR CC κ ω hn]
  constructor
  · intro h
    exact (Nat.pair_eq_pair.mp h).2
  · intro h
    rw [h]

/-- The slice of the race measure over one head outcome carries mass
`A.P a`. -/
theorem RP_slice (hε : 0 < ε) (a₀ : A.Ω) (g : RΩ A BL BR CC κ → ℝ)
    (hg : ∀ (a a' : A.Ω) (l : BL.Ω) (r : BR.Ω) (cc : CC.Ω)
      (χ : Fin κ → Bool), g (a, l, r, cc, χ) = g (a', l, r, cc, χ))
    (a : A.Ω) :
    (∑ l : BL.Ω, ∑ r : BR.Ω, ∑ cc : CC.Ω, ∑ c : Fin κ → Bool,
      RP A BL BR CC κ ε (a, l, r, cc, c) * g (a, l, r, cc, c))
    = A.P a * ∑ l : BL.Ω, ∑ r : BR.Ω, ∑ cc : CC.Ω, ∑ c : Fin κ → Bool,
        BL.P l * (BR.P r * (CC.P cc
          * coinWt (coinW A BL BR a₀ l r (ε := ε)) c))
        * g (a₀, l, r, cc, c) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun cc _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hg a a₀ l r cc c]
  show A.P a * (BL.P l * (BR.P r * (CC.P cc
      * coinWt (coinW A BL BR a l r (ε := ε)) c)))
      * g (a₀, l, r, cc, c) = _
  rw [coinW_indep A BL BR ε a a₀ l r]
  ring

/-- The race expectation of a head-independent function slices as a
constant against the head measure. -/
theorem RP_slice_const (hε : 0 < ε) (a₀ : A.Ω)
    (g : RΩ A BL BR CC κ → ℝ)
    (hg : ∀ (a a' : A.Ω) (l : BL.Ω) (r : BR.Ω) (cc : CC.Ω)
      (χ : Fin κ → Bool), g (a, l, r, cc, χ) = g (a', l, r, cc, χ)) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω * g ω
      = ∑ l : BL.Ω, ∑ r : BR.Ω, ∑ cc : CC.Ω, ∑ c : Fin κ → Bool,
          BL.P l * (BR.P r * (CC.P cc
            * coinWt (coinW A BL BR a₀ l r (ε := ε)) c))
          * g (a₀, l, r, cc, c) := by
  rw [sum_RΩ_expand A BL BR CC κ
    (fun ω => RP A BL BR CC κ ε ω * g ω)]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) =>
    RP_slice A BL BR CC κ ε hε a₀ g hg a]
  rw [← Finset.sum_mul, A.hPsum, one_mul]

/-- Restricted marginalization onto the head system: summing over the
race outcomes whose head lies in `S`. -/
theorem RP_restrict_margA (hε : 0 < ε) (S : Finset A.Ω) (f : A.Ω → ℝ) :
    ∑ ω ∈ Finset.univ.filter
        (fun ω : RΩ A BL BR CC κ => ω.1 ∈ S),
      RP A BL BR CC κ ε ω * f ω.1
    = ∑ a ∈ S, A.P a * f a := by
  classical
  rw [Finset.sum_filter]
  rw [sum_RΩ_expand A BL BR CC κ (fun ω =>
    if ω.1 ∈ S then RP A BL BR CC κ ε ω * f ω.1 else 0)]
  have hsl : ∀ a : A.Ω,
      (∑ l : BL.Ω, ∑ r : BR.Ω, ∑ cc : CC.Ω, ∑ c : Fin κ → Bool,
        if a ∈ S then RP A BL BR CC κ ε (a, l, r, cc, c) * f a else 0)
      = if a ∈ S then A.P a * f a else 0 := by
    intro a
    by_cases haS : a ∈ S
    · simp only [if_pos haS]
      have h1 := RP_slice A BL BR CC κ ε hε a
        (fun _ => (1 : ℝ)) (fun _ _ _ _ _ _ => rfl) a
      have h2 : (∑ l : BL.Ω, ∑ r : BR.Ω, ∑ cc : CC.Ω,
          ∑ c : Fin κ → Bool,
          BL.P l * (BR.P r * (CC.P cc
            * coinWt (coinW A BL BR a l r (ε := ε)) c)) * 1) = 1 := by
        have h3 := RP_slice_const A BL BR CC κ ε hε a
          (fun _ => (1 : ℝ)) (fun _ _ _ _ _ _ => rfl)
        have h4 : ∑ ω : RΩ A BL BR CC κ,
            RP A BL BR CC κ ε ω * (1 : ℝ) = 1 := by
          rw [Finset.sum_congr rfl fun ω (_ : ω ∈ Finset.univ) =>
            mul_one (RP A BL BR CC κ ε ω)]
          exact RP_sum A BL BR CC κ ε hε
        rw [← h3, h4]
      calc (∑ l : BL.Ω, ∑ r : BR.Ω, ∑ cc : CC.Ω, ∑ c : Fin κ → Bool,
            RP A BL BR CC κ ε (a, l, r, cc, c) * f a)
          = (∑ l : BL.Ω, ∑ r : BR.Ω, ∑ cc : CC.Ω, ∑ c : Fin κ → Bool,
              RP A BL BR CC κ ε (a, l, r, cc, c) * (fun _ => (1:ℝ))
                ((a, l, r, cc, c) : RΩ A BL BR CC κ)) * f a := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun cc _ => ?_
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun c _ => by ring
        _ = (A.P a * 1) * f a := by
            rw [RP_slice A BL BR CC κ ε hε a
              (fun _ => (1 : ℝ)) (fun _ _ _ _ _ _ => rfl) a, h2]
        _ = A.P a * f a := by ring
    · simp only [if_neg haS]
      simp
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hsl a]
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp

/-- Restricted head-independent expectation factorizes into the head
mass times the full expectation. -/
theorem RP_restrict_rest (hε : 0 < ε) (S : Finset A.Ω)
    (g : RΩ A BL BR CC κ → ℝ)
    (hg : ∀ (a a' : A.Ω) (l : BL.Ω) (r : BR.Ω) (cc : CC.Ω)
      (χ : Fin κ → Bool), g (a, l, r, cc, χ) = g (a', l, r, cc, χ)) :
    ∑ ω ∈ Finset.univ.filter
        (fun ω : RΩ A BL BR CC κ => ω.1 ∈ S),
      RP A BL BR CC κ ε ω * g ω
    = (∑ a ∈ S, A.P a)
      * ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω * g ω := by
  classical
  obtain ⟨a₀⟩ := omega_nonempty A
  rw [Finset.sum_filter]
  rw [sum_RΩ_expand A BL BR CC κ (fun ω =>
    if ω.1 ∈ S then RP A BL BR CC κ ε ω * g ω else 0)]
  have hsl : ∀ a : A.Ω,
      (∑ l : BL.Ω, ∑ r : BR.Ω, ∑ cc : CC.Ω, ∑ c : Fin κ → Bool,
        if a ∈ S
        then RP A BL BR CC κ ε (a, l, r, cc, c) * g (a, l, r, cc, c)
        else 0)
      = if a ∈ S
        then A.P a * ∑ ω : RΩ A BL BR CC κ,
            RP A BL BR CC κ ε ω * g ω
        else 0 := by
    intro a
    by_cases haS : a ∈ S
    · simp only [if_pos haS]
      rw [RP_slice A BL BR CC κ ε hε a₀ g hg a,
        ← RP_slice_const A BL BR CC κ ε hε a₀ g hg]
    · simp only [if_neg haS]
      simp
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hsl a]
  rw [← Finset.sum_filter, Finset.sum_mul]
  refine Finset.sum_congr ?_ fun a _ => rfl
  ext a
  simp

open Classical in
/-- **The race preserves the head drawdown at head-phase depths**: the
L¹ drawdown of the race total at any depth `n ≤ A.m` equals the head
system's L¹ drawdown at depth `n`, because the race atom is the head
atom and the remaining phases are independent of it. -/
theorem race_drawdown_A (hε : 0 < ε) (hκL : κ ≤ BL.m) (hκR : κ ≤ BR.m)
    {n : ℕ} (hn : n ≤ A.m) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * max ((∑ ω' : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω'
            * ∑ i : Fin (mrace A BL BR CC κ),
                rsize A BL BR CC κ ε ω' (i : ℕ))
          - (∑ ω' ∈ Finset.univ.filter
                (fun ω' : RΩ A BL BR CC κ =>
                  rhist2 A BL BR CC κ ω' n = rhist2 A BL BR CC κ ω n),
              RP A BL BR CC κ ε ω'
                * ∑ i : Fin (mrace A BL BR CC κ),
                    rsize A BL BR CC κ ε ω' (i : ℕ))
            / (∑ ω' ∈ Finset.univ.filter
                (fun ω' : RΩ A BL BR CC κ =>
                  rhist2 A BL BR CC κ ω' n = rhist2 A BL BR CC κ ω n),
              RP A BL BR CC κ ε ω')) 0
      = ∑ a : A.Ω, A.P a
          * max (A.expTotal - A.condExp A.totalSize n a) 0 := by
  -- the head-independent remainder of the race total
  set K : ℝ := ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
    * (gBlock A BL BR CC κ ε ω + ccPart A BL BR CC κ ω) with hK
  have hgcong : ∀ (a a' : A.Ω) (l : BL.Ω) (r : BR.Ω) (cc : CC.Ω)
      (χ : Fin κ → Bool),
      gBlock A BL BR CC κ ε (a, l, r, cc, χ)
          + ccPart A BL BR CC κ (a, l, r, cc, χ)
        = gBlock A BL BR CC κ ε (a', l, r, cc, χ)
          + ccPart A BL BR CC κ (a', l, r, cc, χ) := by
    intro a a' l r cc χ
    rw [gBlock_congr A BL BR CC κ ε a a' l r cc cc χ]
    rfl
  -- decompose the race total pathwise
  have hdecomp : ∀ ω' : RΩ A BL BR CC κ,
      (∑ i : Fin (mrace A BL BR CC κ),
        rsize A BL BR CC κ ε ω' (i : ℕ))
      = preSum A ω'.1 A.m
        + (gBlock A BL BR CC κ ε ω' + ccPart A BL BR CC κ ω') := by
    intro ω'
    rw [rsum_decomp A BL BR CC κ ε hκL hκR ω']
    unfold gBlock
    ring
  -- the full expected race total
  have hEtot : ∑ ω' : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω'
      * ∑ i : Fin (mrace A BL BR CC κ), rsize A BL BR CC κ ε ω' (i : ℕ)
      = A.expTotal + K := by
    rw [Finset.sum_congr rfl fun ω' (_ : ω' ∈ Finset.univ) =>
      show RP A BL BR CC κ ε ω'
          * ∑ i : Fin (mrace A BL BR CC κ),
              rsize A BL BR CC κ ε ω' (i : ℕ)
        = RP A BL BR CC κ ε ω' * preSum A ω'.1 A.m
          + RP A BL BR CC κ ε ω'
            * (gBlock A BL BR CC κ ε ω' + ccPart A BL BR CC κ ω')
        from by rw [hdecomp ω']; ring, Finset.sum_add_distrib, ← hK]
    congr 1
    rw [RP_margA A BL BR CC κ ε hε (fun a => preSum A a A.m)]
    unfold ChunkSystemB.expTotal
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [preSum_total]
    rfl
  -- the per-atom conditional of the race total
  have hcond : ∀ ω : RΩ A BL BR CC κ,
      (∑ ω' ∈ Finset.univ.filter
          (fun ω' : RΩ A BL BR CC κ =>
            rhist2 A BL BR CC κ ω' n = rhist2 A BL BR CC κ ω n),
        RP A BL BR CC κ ε ω'
          * ∑ i : Fin (mrace A BL BR CC κ),
              rsize A BL BR CC κ ε ω' (i : ℕ))
        / (∑ ω' ∈ Finset.univ.filter
            (fun ω' : RΩ A BL BR CC κ =>
              rhist2 A BL BR CC κ ω' n = rhist2 A BL BR CC κ ω n),
          RP A BL BR CC κ ε ω')
      = A.condExp A.totalSize n ω.1 + K := by
    intro ω
    rw [race_atom_A A BL BR CC κ hn ω]
    have hSfst : Finset.univ.filter (fun ω' : RΩ A BL BR CC κ =>
        A.hist n ω'.1 = A.hist n ω.1)
        = Finset.univ.filter (fun ω' : RΩ A BL BR CC κ =>
          ω'.1 ∈ A.atom n ω.1) := by
      ext ω'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        ChunkSystemB.mem_atom]
    rw [hSfst]
    have hnum : ∑ ω' ∈ Finset.univ.filter
        (fun ω' : RΩ A BL BR CC κ => ω'.1 ∈ A.atom n ω.1),
        RP A BL BR CC κ ε ω'
          * ∑ i : Fin (mrace A BL BR CC κ),
              rsize A BL BR CC κ ε ω' (i : ℕ)
        = (∑ a ∈ A.atom n ω.1, A.P a * preSum A a A.m)
          + (∑ a ∈ A.atom n ω.1, A.P a) * K := by
      rw [Finset.sum_congr rfl fun ω' (_ : ω' ∈ Finset.univ.filter
          (fun ω' : RΩ A BL BR CC κ => ω'.1 ∈ A.atom n ω.1)) =>
        show RP A BL BR CC κ ε ω'
            * ∑ i : Fin (mrace A BL BR CC κ),
                rsize A BL BR CC κ ε ω' (i : ℕ)
          = RP A BL BR CC κ ε ω' * preSum A ω'.1 A.m
            + RP A BL BR CC κ ε ω'
              * (gBlock A BL BR CC κ ε ω' + ccPart A BL BR CC κ ω')
          from by rw [hdecomp ω']; ring, Finset.sum_add_distrib]
      congr 1
      · exact RP_restrict_margA A BL BR CC κ ε hε (A.atom n ω.1)
          (fun a => preSum A a A.m)
      · rw [RP_restrict_rest A BL BR CC κ ε hε (A.atom n ω.1)
          (fun ω' => gBlock A BL BR CC κ ε ω' + ccPart A BL BR CC κ ω')
          hgcong, ← hK]
    have hden : ∑ ω' ∈ Finset.univ.filter
        (fun ω' : RΩ A BL BR CC κ => ω'.1 ∈ A.atom n ω.1),
        RP A BL BR CC κ ε ω'
        = ∑ a ∈ A.atom n ω.1, A.P a := by
      have h1 := RP_restrict_margA A BL BR CC κ ε hε (A.atom n ω.1)
        (fun _ => (1 : ℝ))
      rw [Finset.sum_congr rfl fun ω' (_ : ω' ∈ Finset.univ.filter
          (fun ω' : RΩ A BL BR CC κ => ω'.1 ∈ A.atom n ω.1)) =>
        (mul_one (RP A BL BR CC κ ε ω')).symm, h1]
      exact Finset.sum_congr rfl fun a _ => mul_one (A.P a)
    rw [hnum, hden]
    have hmass : (0 : ℝ) < ∑ a ∈ A.atom n ω.1, A.P a :=
      A.mass_atom_pos n ω.1
    rw [add_div, mul_div_cancel_left₀ K (ne_of_gt hmass)]
    congr 1
    unfold ChunkSystemB.condExp ChunkSystemB.mass
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [preSum_total]
    rfl
  -- assemble
  rw [Finset.sum_congr rfl fun ω (_ : ω ∈ Finset.univ) => by
    rw [hcond ω, hEtot]]
  have hptmax : ∀ ω : RΩ A BL BR CC κ,
      max (A.expTotal + K - (A.condExp A.totalSize n ω.1 + K)) 0
      = max (A.expTotal - A.condExp A.totalSize n ω.1) 0 := by
    intro ω
    congr 1
    ring
  rw [Finset.sum_congr rfl fun ω (_ : ω ∈ Finset.univ) => by
    rw [hptmax ω]]
  exact RP_margA A BL BR CC κ ε hε
    (fun a => max (A.expTotal - A.condExp A.totalSize n a) 0)

open Classical in
/-- **The race preserves the head bad-chunk counts at head-phase
depths**: the expected number of below-floor chunks among the first
`n' ≤ A.m` race chunks equals the head system's expected count. -/
theorem race_badcount_A (hε : 0 < ε) (flo : ℝ) {n' : ℕ}
    (hn' : n' ≤ A.m) :
    ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * (∑ i ∈ Finset.range n',
          if rsize A BL BR CC κ ε ω i < flo then (1 : ℝ) else 0)
    = ∑ a : A.Ω, A.P a * (∑ i ∈ Finset.range n',
        if A.sizeN i a < flo then (1 : ℝ) else 0) := by
  have hpt : ∀ ω : RΩ A BL BR CC κ, ∀ i ∈ Finset.range n',
      (if rsize A BL BR CC κ ε ω i < flo then (1 : ℝ) else 0)
      = (if A.sizeN i ω.1 < flo then (1 : ℝ) else 0) := by
    intro ω i hi
    rw [Finset.mem_range] at hi
    have hiA : i < A.m := lt_of_lt_of_le hi hn'
    have hr : rsize A BL BR CC κ ε ω i = A.sizeN i ω.1 := by
      unfold rsize
      rw [if_pos hiA]
    rw [hr]
  rw [Finset.sum_congr rfl fun ω (_ : ω ∈ Finset.univ) => by
    rw [Finset.sum_congr rfl (hpt ω)]]
  exact RP_margA A BL BR CC κ ε hε
    (fun a => ∑ i ∈ Finset.range n',
      if A.sizeN i a < flo then (1 : ℝ) else 0)

end SturdyOut

end Race

end KServer


