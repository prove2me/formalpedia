-- Prove2me | solution 1 for CRTSplitNoGo.average_closureTime_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T19:58:15.162365+00:00
-- url     : https://prove2.me/submissions/1ad8e768-676f-4e27-9faa-0b30359e0c37

import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGoAverage

open CRTSplitNoGo Finset in
theorem solution {α : Type*} [Fintype α] [DecidableEq α] (a : α) (T : ℕ)
    (hT : T < Fintype.card α) (h : T * (T + 1) ≤ Fintype.card α) :
    ((T : ℝ) + 1) * ((Fintype.card α : ℝ) ^ (Fintype.card α) / 2)
      ≤ ∑ f : α → α, (closureTime a f : ℝ) := by
  classical
  have horb_succ : ∀ (f : α → α) (i : ℕ), orb f a (i + 1) = f (orb f a i) := by
    intro f i
    simp only [orb, Function.iterate_succ_apply']
  have hmem : ∀ (f : α → α) (S : ℕ), f ∈ injPrefixFinset a S ↔ InjPrefix f a S := by
    intro f S
    simp [injPrefixFinset]
  -- updating `f` at the last prefix point does not move the prefix
  have hL1 : ∀ (f : α → α) (S : ℕ), InjPrefix f a S → ∀ v, ∀ i ≤ S,
      orb (Function.update f (orb f a S) v) a i = orb f a i := by
    intro f S hf v i hi
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [horb_succ, horb_succ, ih (by omega), Function.update_of_ne]
      intro h
      have := hf i (by omega) S le_rfl h
      omega
  have hL2 : ∀ (f : α → α) (S : ℕ), InjPrefix f a S → ∀ v,
      InjPrefix (Function.update f (orb f a S) v) a S := by
    intro f S hf v i hi j hj h
    rw [hL1 f S hf v i hi, hL1 f S hf v j hj] at h
    exact hf i hi j hj h
  have hlast : ∀ (f : α → α) (S : ℕ), InjPrefix f a S → ∀ v,
      orb (Function.update f (orb f a S) v) a (S + 1) = v := by
    intro f S hf v
    rw [horb_succ, hL1 f S hf v S le_rfl, Function.update_self]
  have hL3 : ∀ (f : α → α) (S : ℕ), InjPrefix f a S → ∀ v,
      InjPrefix (Function.update f (orb f a S) v) a (S + 1) ↔ ∀ i ≤ S, v ≠ orb f a i := by
    intro f S hf v
    constructor
    · intro h i hi hv
      have h1 := hlast f S hf v
      have h2 := hL1 f S hf v i hi
      have := h (S + 1) le_rfl i (by omega) (by rw [h1, h2, hv])
      omega
    · intro hv i hi j hj h
      rcases Nat.lt_or_ge i (S + 1) with hi' | hi' <;>
        rcases Nat.lt_or_ge j (S + 1) with hj' | hj'
      · exact hL2 f S hf v i (by omega) j (by omega) h
      · have hjS : j = S + 1 := by omega
        subst hjS
        rw [hlast f S hf v, hL1 f S hf v i (by omega)] at h
        exact absurd h.symm (hv i (by omega))
      · have hiS : i = S + 1 := by omega
        subst hiS
        rw [hlast f S hf v, hL1 f S hf v j (by omega)] at h
        exact absurd h (hv j (by omega))
      · omega
  have hreset : ∀ (f : α → α) (S : ℕ), InjPrefix f a S → ∀ v,
      reset a S (Function.update f (orb f a S) v) = reset a S f := by
    intro f S hf v
    unfold reset
    rw [hL1 f S hf v S le_rfl, Function.update_idem]
  have hL5 : ∀ (f f' : α → α) (S : ℕ), InjPrefix f a S → InjPrefix f' a S →
      reset a S f = reset a S f' → f' = Function.update f (orb f a S) (f' (orb f a S)) := by
    intro f f' S hf hf' h
    have hx : orb f a S = orb f' a S := by
      have e1 := hL1 f S hf a S le_rfl
      have e2 := hL1 f' S hf' a S le_rfl
      unfold reset at h
      rw [← e1, ← e2, h]
    funext y
    by_cases hy : y = orb f a S
    · subst hy
      rw [Function.update_self]
    · rw [Function.update_of_ne hy]
      have h1 := congrFun h y
      unfold reset at h1
      rw [Function.update_of_ne hy, Function.update_of_ne (hx ▸ hy)] at h1
      exact h1.symm
  -- the recursion `|S(T+1)| · N = |S(T)| · (N - (T+1))`
  have hstep : ∀ S : ℕ, S + 1 < Fintype.card α →
      (injPrefixFinset a (S + 1)).card * Fintype.card α
        = (injPrefixFinset a S).card * (Fintype.card α - (S + 1)) := by
    intro S hS
    set t := (injPrefixFinset a S).image (reset a S) with ht
    have hsub : injPrefixFinset a (S + 1) ⊆ injPrefixFinset a S := by
      intro f hf
      rw [hmem] at hf ⊢
      exact fun i hi j hj h => hf i (by omega) j (by omega) h
    -- fibre sizes over each `h ∈ t`
    have hfibT : ∀ h ∈ t, ((injPrefixFinset a S).filter (fun f => reset a S f = h)).card
        = Fintype.card α := by
      intro h hh
      obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.1 hh
      rw [hmem] at hf0
      have heq : (injPrefixFinset a S).filter (fun f => reset a S f = reset a S f0)
          = univ.image (fun v => Function.update f0 (orb f0 a S) v) := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, hmem]
        constructor
        · rintro ⟨hg, hgr⟩
          exact ⟨g (orb f0 a S), (hL5 f0 g S hf0 hg hgr.symm).symm⟩
        · rintro ⟨v, rfl⟩
          exact ⟨hL2 f0 S hf0 v, hreset f0 S hf0 v⟩
      rw [heq, Finset.card_image_of_injective, Finset.card_univ]
      intro v w hvw
      have := congrFun hvw (orb f0 a S)
      simpa using this
    have hfibT1 : ∀ h ∈ t, ((injPrefixFinset a (S + 1)).filter (fun f => reset a S f = h)).card
        = Fintype.card α - (S + 1) := by
      intro h hh
      obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.1 hh
      rw [hmem] at hf0
      have heq : (injPrefixFinset a (S + 1)).filter (fun f => reset a S f = reset a S f0)
          = (univ.filter (fun v => ∀ i ≤ S, v ≠ orb f0 a i)).image
              (fun v => Function.update f0 (orb f0 a S) v) := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, hmem]
        constructor
        · rintro ⟨hg, hgr⟩
          have hgS : InjPrefix g a S := fun i hi j hj h => hg i (by omega) j (by omega) h
          have hgeq := hL5 f0 g S hf0 hgS hgr.symm
          refine ⟨g (orb f0 a S), ?_, hgeq.symm⟩
          rw [hgeq] at hg
          exact (hL3 f0 S hf0 _).1 hg
        · rintro ⟨v, hv, rfl⟩
          exact ⟨(hL3 f0 S hf0 v).2 hv, hreset f0 S hf0 v⟩
      rw [heq, Finset.card_image_of_injective]
      · have hcompl : univ.filter (fun v => ∀ i ≤ S, v ≠ orb f0 a i)
            = univ \ (range (S + 1)).image (orb f0 a) := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
            Finset.mem_image, Finset.mem_range, not_exists, not_and]
          constructor
          · intro h i hi hv
            exact h i (by omega) hv.symm
          · intro h i hi hv
            exact h i (by omega) hv.symm
        rw [hcompl, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
          Finset.card_image_of_injOn, Finset.card_range]
        intro i hi j hj h
        simp only [Finset.coe_range, Set.mem_Iio] at hi hj
        exact hf0 i (by omega) j (by omega) h
      · intro v w hvw
        have := congrFun hvw (orb f0 a S)
        simpa using this
    have hA := Finset.card_eq_sum_card_fiberwise (f := reset a S) (s := injPrefixFinset a S)
      (t := t) (fun f hf => Finset.mem_coe.2 (Finset.mem_image_of_mem _ hf))
    have hB := Finset.card_eq_sum_card_fiberwise (f := reset a S)
      (s := injPrefixFinset a (S + 1)) (t := t)
      (fun f hf => Finset.mem_coe.2 (Finset.mem_image_of_mem _ (hsub hf)))
    rw [Finset.sum_congr rfl hfibT, Finset.sum_const, smul_eq_mul] at hA
    rw [Finset.sum_congr rfl hfibT1, Finset.sum_const, smul_eq_mul] at hB
    rw [hA, hB]
    ring
  -- closed form by induction on the prefix length
  have hmain : ∀ S : ℕ, S < Fintype.card α → (injPrefixFinset a S).card
      = (Fintype.card α - 1).descFactorial S * (Fintype.card α) ^ (Fintype.card α - S) := by
    intro S
    induction S with
    | zero =>
      intro _
      have huniv : injPrefixFinset a 0 = univ := by
        ext f
        simp only [Finset.mem_univ, iff_true, hmem]
        intro i hi j hj _
        omega
      rw [huniv, Finset.card_univ, Fintype.card_fun, Nat.descFactorial_zero, one_mul,
        Nat.sub_zero]
    | succ S ih =>
      intro hS
      have hN : 0 < Fintype.card α := by omega
      have h1 := hstep S hS
      rw [ih (by omega)] at h1
      apply Nat.eq_of_mul_eq_mul_right hN
      rw [h1, Nat.descFactorial_succ]
      have e : Fintype.card α - S = (Fintype.card α - (S + 1)) + 1 := by omega
      rw [e, pow_succ]
      have e2 : Fintype.card α - 1 - S = Fintype.card α - (S + 1) := by omega
      rw [e2]
      ring
  -- product form
  have hprod : ∀ S : ℕ, S < Fintype.card α → ((injPrefixFinset a S).card : ℝ)
      = (∏ i ∈ Finset.range S, (1 - ((i : ℝ) + 1) / Fintype.card α))
          * (Fintype.card α : ℝ) ^ (Fintype.card α) := by
    intro S hS
    have hNpos : (0 : ℝ) < Fintype.card α := by exact_mod_cast (show 0 < Fintype.card α by omega)
    rw [hmain S hS, Nat.descFactorial_eq_prod_range]
    push_cast
    have hfac : ∀ i ∈ Finset.range S, (1 - ((i : ℝ) + 1) / Fintype.card α)
        = ((Fintype.card α - 1 - i : ℕ) : ℝ) / Fintype.card α := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      field_simp
      ring
    rw [Finset.prod_congr rfl hfac, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
    have hpow : (Fintype.card α : ℝ) ^ (Fintype.card α)
        = (Fintype.card α : ℝ) ^ S * (Fintype.card α : ℝ) ^ (Fintype.card α - S) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    have hS0 : (Fintype.card α : ℝ) ^ S ≠ 0 := pow_ne_zero _ hNpos.ne'
    field_simp
  have hn : 0 < Fintype.card α := Fintype.card_pos_iff.2 ⟨a⟩
  have hNpos : (0 : ℝ) < Fintype.card α := by exact_mod_cast hn
  have hgauss : ∀ S : ℕ, ∑ i ∈ Finset.range S, ((i : ℝ) + 1) / Fintype.card α
      = (S * (S + 1) : ℝ) / (2 * Fintype.card α) := by
    intro S
    induction S with
    | zero => simp
    | succ S ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp
      ring
  have hST : ∀ S : ℕ, S < Fintype.card α → ((injPrefixFinset a S).card : ℝ)
      ≤ Real.exp (-((S * (S + 1) : ℝ) / (2 * Fintype.card α)))
          * (Fintype.card α : ℝ) ^ (Fintype.card α) := by
    intro S hS
    have hx : ∀ i ∈ Finset.range S, 0 ≤ ((i : ℝ) + 1) / Fintype.card α ∧
        ((i : ℝ) + 1) / Fintype.card α ≤ 1 := by
      intro i hi
      rw [Finset.mem_range] at hi
      refine ⟨by positivity, ?_⟩
      rw [div_le_one hNpos]
      have : (i : ℝ) + 1 ≤ S := by exact_mod_cast hi
      have hS' : (S : ℝ) < Fintype.card α := by exact_mod_cast hS
      linarith
    have hexpb : ∏ i ∈ Finset.range S, (1 - ((i : ℝ) + 1) / Fintype.card α)
        ≤ Real.exp (-((S * (S + 1) : ℝ) / (2 * Fintype.card α))) := by
      rw [← hgauss S, ← Finset.sum_neg_distrib, Real.exp_sum]
      refine Finset.prod_le_prod (fun i hi => by linarith [(hx i hi).2]) (fun i _ => ?_)
      linarith [Real.add_one_le_exp (-(((i : ℝ) + 1) / Fintype.card α))]
    rw [hprod S hS]
    exact mul_le_mul_of_nonneg_right hexpb (by positivity)
  -- the closure time counts the collision-free prefixes
  have hanti : ∀ (f : α → α) (S T : ℕ), S ≤ T → InjPrefix f a T → InjPrefix f a S :=
    fun f S T hST hT i hi j hj h => hT i (hi.trans hST) j (hj.trans hST) h
  have hpig : ∀ f : α → α, ¬ InjPrefix f a (Fintype.card α) := by
    intro f hf
    obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (Fintype.card α + 1)) (t := (Finset.univ : Finset α)) (f := orb f a)
      (by simp) (fun _ _ => Finset.mem_univ _)
    rw [Finset.mem_range] at hi hj
    exact hij (hf i (by omega) j (by omega) heq)
  have hct_le : ∀ f : α → α, closureTime a f ≤ Fintype.card α :=
    fun f => Nat.sInf_le (s := {T : ℕ | ¬ InjPrefix f a T}) (hpig f)
  have hchar : ∀ (f : α → α) (T : ℕ), InjPrefix f a T ↔ T < closureTime a f := by
    intro f T
    constructor
    · intro hT
      by_contra hlt
      have hle : closureTime a f ≤ T := not_lt.1 hlt
      have hmemS : ¬ InjPrefix f a (closureTime a f) :=
        Nat.sInf_mem (s := {T : ℕ | ¬ InjPrefix f a T}) ⟨_, hpig f⟩
      exact hmemS (hanti f _ _ hle hT)
    · intro hlt
      have := Nat.notMem_of_lt_sInf (s := {T : ℕ | ¬ InjPrefix f a T}) hlt
      simpa using this
  have hcount : ∀ f : α → α, closureTime a f
      = ((Finset.range (Fintype.card α)).filter (fun T => f ∈ injPrefixFinset a T)).card := by
    intro f
    have h : (Finset.range (Fintype.card α)).filter (fun T => f ∈ injPrefixFinset a T)
        = Finset.range (closureTime a f) := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_range, hmem, hchar]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨lt_of_lt_of_le h (hct_le f), h⟩
    rw [h, Finset.card_range]
  have hsum : ∑ f : α → α, (closureTime a f : ℝ)
      = ∑ T ∈ Finset.range (Fintype.card α), ((injPrefixFinset a T).card : ℝ) := by
    have hnat : ∑ f : α → α, closureTime a f
        = ∑ T ∈ Finset.range (Fintype.card α), (injPrefixFinset a T).card := by
      simp_rw [hcount, Finset.card_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun T _ => ?_)
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]
    exact_mod_cast hnat
  have hweier : ∀ (s : Finset ℕ) (x : ℕ → ℝ), (∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1) →
      1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
    intro s x hx
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.prod_insert hj]
      have hxj := hx j (Finset.mem_insert_self j s)
      have ih' := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
      have hS : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg fun i hi =>
        (hx i (Finset.mem_insert_of_mem hi)).1
      nlinarith
  have hmain : ∀ T : ℕ, T < Fintype.card α → T * (T + 1) ≤ Fintype.card α →
      ((T : ℝ) + 1) * ((Fintype.card α : ℝ) ^ (Fintype.card α) / 2)
        ≤ ∑ f : α → α, (closureTime a f : ℝ) := by
    intro T hT h
    have hlow : ∀ S : ℕ, S ≤ T → (Fintype.card α : ℝ) ^ (Fintype.card α) / 2
        ≤ ((injPrefixFinset a S).card : ℝ) := by
      intro S hS
      have hSN : S < Fintype.card α := by omega
      have hx : ∀ i ∈ Finset.range S, 0 ≤ ((i : ℝ) + 1) / Fintype.card α ∧
          ((i : ℝ) + 1) / Fintype.card α ≤ 1 := by
        intro i hi
        rw [Finset.mem_range] at hi
        refine ⟨by positivity, ?_⟩
        rw [div_le_one hNpos]
        have : (i : ℝ) + 1 ≤ S := by exact_mod_cast hi
        have hS' : (S : ℝ) < Fintype.card α := by exact_mod_cast hSN
        linarith
      rw [hprod S hSN]
      have hw := hweier _ _ hx
      rw [hgauss S] at hw
      have hSS : (S : ℝ) * (S + 1) ≤ T * (T + 1) := by
        have : S * (S + 1) ≤ T * (T + 1) := Nat.mul_le_mul hS (by omega)
        exact_mod_cast this
      have hTN : (T : ℝ) * (T + 1) ≤ Fintype.card α := by exact_mod_cast h
      have hfrac : (S * (S + 1) : ℝ) / (2 * Fintype.card α) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      have hpg : (1 : ℝ) / 2 ≤ ∏ i ∈ Finset.range S, (1 - ((i : ℝ) + 1) / Fintype.card α) := by
        linarith
      have hNN : (0 : ℝ) ≤ (Fintype.card α : ℝ) ^ (Fintype.card α) := by positivity
      calc (Fintype.card α : ℝ) ^ (Fintype.card α) / 2
          = (1 / 2) * (Fintype.card α : ℝ) ^ (Fintype.card α) := by ring
        _ ≤ (∏ i ∈ Finset.range S, (1 - ((i : ℝ) + 1) / Fintype.card α))
              * (Fintype.card α : ℝ) ^ (Fintype.card α) := mul_le_mul_of_nonneg_right hpg hNN
    rw [hsum]
    calc ((T : ℝ) + 1) * ((Fintype.card α : ℝ) ^ (Fintype.card α) / 2)
        = ∑ S ∈ Finset.range (T + 1), (Fintype.card α : ℝ) ^ (Fintype.card α) / 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ ∑ S ∈ Finset.range (T + 1), ((injPrefixFinset a S).card : ℝ) :=
          Finset.sum_le_sum (fun S hS => hlow S (by rw [Finset.mem_range] at hS; omega))
      _ ≤ ∑ S ∈ Finset.range (Fintype.card α), ((injPrefixFinset a S).card : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx => by rw [Finset.mem_range] at hx ⊢; omega) (fun _ _ _ => Nat.cast_nonneg _)
  exact hmain T hT h
