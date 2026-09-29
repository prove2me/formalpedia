-- Prove2me | solution 1 for KServer.bcr_tight_base
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-07T21:33:36.363399+00:00
-- url     : https://prove2.me/submissions/8e03c0c3-facd-4bc4-afb7-a256f2a8ade9

import Mathlib
import Definitions.Def_KServer_bcr_induction_tight

set_option autoImplicit false
set_option maxHeartbeats 1000000

open KServer

namespace BCRBase

/-- `Geo s t N`: there is a unit-spaced isometric chain of `N + 1` points
running from `s` to `t`. -/
def Geo {X : Type*} [MetricSpace X] (s t : X) (N : ℕ) : Prop :=
  ∃ g : ℕ → X, g 0 = s ∧ g N = t ∧
    ∀ i, i ≤ N → ∀ j, j ≤ N → dist (g i) (g j) = |(i : ℝ) - (j : ℝ)|

/-- Level `0` of the BCR family is the path of `β + 1` points, which is itself
a unit geodesic chain. -/
theorem geo_path (β : ℕ) :
    letI := pathMetric β
    Geo (0 : Fin (β + 1)) (Fin.last β) β := by
  letI := pathMetric β
  have hdist : ∀ a b : Fin (β + 1), dist a b = |(a.val : ℝ) - (b.val : ℝ)| :=
    fun _ _ => rfl
  refine ⟨fun n => ⟨min n β, by omega⟩, ?_, ?_, ?_⟩
  · exact Fin.ext (by simp)
  · exact Fin.ext (by simp [Fin.last])
  · intro i hi j hj
    rw [hdist]
    simp only []
    rw [show min i β = i by omega, show min j β = j by omega]

/-- The unit geodesic chain survives one BCR level step: the theta gluing of
two three-copy paths contains a chain of `3N + 1` unit-spaced points from
`stepS` to `stepT`. -/
theorem geo_step {X : Type*} [MetricSpace X] (s t : X) (hst : s ≠ t) (N : ℕ)
    (hN : 1 ≤ N) (h : Geo s t N) :
    letI := ThetaChain.stepMetric s t hst
    Geo (ThetaChain.stepS s t hst) (ThetaChain.stepT s t hst) (3 * N) := by
  classical
  obtain ⟨g, hg0, hgN, hgd⟩ := h
  letI := chain3Metric X s t hst
  -- basic distances in the base chain
  have hgs : ∀ i, i ≤ N → dist s (g i) = (i : ℝ) := by
    intro i hi
    rw [← hg0, hgd 0 (by omega) i hi]
    simp
  have hgt : ∀ i, i ≤ N → dist (g i) t = (N : ℝ) - (i : ℝ) := by
    intro i hi
    rw [← hgN, hgd i hi N (le_refl _)]
    rw [abs_of_nonpos (by
      have : (i : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
      linarith)]
    ring
  have hgne : ∀ i, 1 ≤ i → i ≤ N → g i ≠ s := by
    intro i h1 h2 hcon
    have := hgs i h2
    rw [hcon, dist_self] at this
    have : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast h1
    linarith [hgs i h2, hcon]
  have hgnet : t ≠ s := hst.symm
  -- the chain in the three-copy path
  set ph : ℕ → Chain3Point X s t := fun n =>
    if hn : n ≤ N then Chain3.emb0 s t (g n)
    else if hn2 : n ≤ 2 * N then
      Chain3.emb1 s t (g (n - N)) (hgne (n - N) (by omega) (by omega))
    else
      Chain3.emb2 s t (g (min (n - 2 * N) N))
        (by
          by_cases hle : n - 2 * N ≤ N
          · exact hgne (min (n - 2 * N) N) (by omega) (by omega)
          · rw [show min (n - 2 * N) N = N by omega, hgN]
            exact hgnet) with hph
  -- distances along the three-copy chain, for `n ≤ m`
  have key : ∀ n m, n ≤ m → m ≤ 3 * N →
      dist (ph n) (ph m) = (m : ℝ) - (n : ℝ) := by
    intro n m hnm hm
    have hn : n ≤ 3 * N := by omega
    by_cases h1 : n ≤ N
    · by_cases h2 : m ≤ N
      · rw [hph]
        simp only [dif_pos h1, dif_pos h2]
        rw [Chain3.dist_emb0_emb0 s t hst]
        rw [hgd n h1 m h2, abs_of_nonpos (by
          have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
          linarith)]
        ring
      · by_cases h3 : m ≤ 2 * N
        · rw [hph]
          simp only [dif_pos h1, dif_neg h2, dif_pos h3]
          rw [Chain3.dist_emb0_emb1 s t hst]
          rw [hgt n h1, hgs (m - N) (by omega)]
          have : ((m - N : ℕ) : ℝ) = (m : ℝ) - (N : ℝ) := by
            have : N ≤ m := by omega
            push_cast [Nat.cast_sub this]
            ring
          rw [this]; ring
        · rw [hph]
          simp only [dif_pos h1, dif_neg h2, dif_neg h3]
          rw [Chain3.dist_emb0_emb2 s t hst,
            show min (m - 2 * N) N = m - 2 * N by omega]
          rw [hgt n h1, hgs (m - 2 * N) (by omega)]
          have hNm : 2 * N ≤ m := by omega
          have : ((m - 2 * N : ℕ) : ℝ) = (m : ℝ) - 2 * (N : ℝ) := by
            push_cast [Nat.cast_sub hNm]
            ring
          rw [this]
          have hst' : dist s t = (N : ℝ) := by
            rw [← hg0, ← hgN, hgd 0 (by omega) N (le_refl _)]
            simp
          rw [hst']; ring
    · by_cases h2 : n ≤ 2 * N
      · by_cases h3 : m ≤ 2 * N
        · rw [hph]
          simp only [dif_neg h1, dif_pos h2, dif_neg (show ¬ m ≤ N by omega), dif_pos h3]
          rw [Chain3.dist_emb1_emb1 s t hst]
          rw [hgd (n - N) (by omega) (m - N) (by omega)]
          have e1 : ((n - N : ℕ) : ℝ) = (n : ℝ) - (N : ℝ) := by
            push_cast [Nat.cast_sub (show N ≤ n by omega)]; ring
          have e2 : ((m - N : ℕ) : ℝ) = (m : ℝ) - (N : ℝ) := by
            push_cast [Nat.cast_sub (show N ≤ m by omega)]; ring
          rw [e1, e2, abs_of_nonpos (by
            have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
            linarith)]
          ring
        · rw [hph]
          simp only [dif_neg h1, dif_pos h2, dif_neg (show ¬ m ≤ N by omega), dif_neg h3]
          rw [Chain3.dist_emb1_emb2 s t hst,
            show min (m - 2 * N) N = m - 2 * N by omega]
          rw [hgt (n - N) (by omega), hgs (m - 2 * N) (by omega)]
          have e1 : ((n - N : ℕ) : ℝ) = (n : ℝ) - (N : ℝ) := by
            push_cast [Nat.cast_sub (show N ≤ n by omega)]; ring
          have e2 : ((m - 2 * N : ℕ) : ℝ) = (m : ℝ) - 2 * (N : ℝ) := by
            push_cast [Nat.cast_sub (show 2 * N ≤ m by omega)]; ring
          rw [e1, e2]; ring
      · rw [hph]
        simp only [dif_neg h1, dif_neg h2,
          dif_neg (show ¬ m ≤ N by omega), dif_neg (show ¬ m ≤ 2 * N by omega)]
        rw [Chain3.dist_emb2_emb2 s t hst,
          show min (m - 2 * N) N = m - 2 * N by omega,
          show min (n - 2 * N) N = n - 2 * N by omega]
        rw [hgd (n - 2 * N) (by omega) (m - 2 * N) (by omega)]
        have e1 : ((n - 2 * N : ℕ) : ℝ) = (n : ℝ) - 2 * (N : ℝ) := by
          push_cast [Nat.cast_sub (show 2 * N ≤ n by omega)]; ring
        have e2 : ((m - 2 * N : ℕ) : ℝ) = (m : ℝ) - 2 * (N : ℝ) := by
          push_cast [Nat.cast_sub (show 2 * N ≤ m by omega)]; ring
        rw [e1, e2, abs_of_nonpos (by
          have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
          linarith)]
        ring
  -- endpoints
  have hph0 : ph 0 = Chain3.start s t := by
    rw [hph]
    simp only [dif_pos (Nat.zero_le N)]
    rw [hg0]
    rfl
  have hphN : ph (3 * N) = Chain3.stop s t hst := by
    rw [hph]
    simp only [dif_neg (show ¬ 3 * N ≤ N by omega),
      dif_neg (show ¬ 3 * N ≤ 2 * N by omega)]
    show (Sum.inr ⟨g (min (3 * N - 2 * N) N), _⟩ : Chain3Point X s t)
      = Sum.inr ⟨t, hst.symm⟩
    congr 1
    refine Subtype.ext ?_
    show g (min (3 * N - 2 * N) N) = t
    rw [show min (3 * N - 2 * N) N = N by omega, hgN]
  -- transfer to the theta gluing
  letI := ThetaChain.stepMetric s t hst
  have hthe : ∀ u v : Chain3Point X s t,
      dist (Sum.inl u : ThetaChain.Step s t hst) (Sum.inl v) = dist u v := by
    intro u v
    show ThetaPoint.dist' (Chain3.start s t) (Chain3.stop s t hst)
      (Sum.inl u) (Sum.inl v) = _
    unfold ThetaPoint.dist'
    exact thetaDist_same _ _ false u v
  refine ⟨fun n => Sum.inl (ph n), ?_, ?_, ?_⟩
  · show (Sum.inl (ph 0) : ThetaChain.Step s t hst) = ThetaChain.stepS s t hst
    rw [hph0]; rfl
  · show (Sum.inl (ph (3 * N)) : ThetaChain.Step s t hst) = ThetaChain.stepT s t hst
    rw [hphN]; rfl
  · intro i hi j hj
    rw [hthe]
    rcases le_total i j with hij | hij
    · rw [key i j hij hj, abs_of_nonpos (by
        have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
        linarith)]
      ring
    · rw [dist_comm, key j i hij hi, abs_of_nonneg (by
        have : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast hij
        linarith)]

/-- Every level of the corrected BCR family carries a unit geodesic chain of
`β · 3 ^ w + 1` points between its marked points. -/
theorem geo_bcrLevel2 (β : ℕ) (hβ : 0 < β) (w : ℕ) :
    Geo (bcrLevel2 β hβ w).s (bcrLevel2 β hβ w).t (β * 3 ^ w) := by
  induction w with
  | zero =>
    have h := geo_path β
    simpa using h
  | succ w ih =>
    have h := geo_step (bcrLevel2 β hβ w).s (bcrLevel2 β hβ w).t
      (bcrLevel2 β hβ w).hst (β * 3 ^ w) (Nat.mul_pos hβ (pow_pos (by norm_num) w)) ih
    have he : β * 3 ^ (w + 1) = 3 * (β * 3 ^ w) := by ring
    rw [he]
    exact h


/-! ### The cruel single-file adversary along a geodesic chain -/

theorem ecost_concat {M : Type*} [MetricSpace M]
    (E : EvaderAlgorithm M) (l : List (Set M)) (S : Set M) :
    E.cost (l ++ [S]) = E.cost l + dist (E.pos l) (E.pos (l ++ [S])) := by
  unfold EvaderAlgorithm.cost
  have hlen : (l ++ [S]).length = l.length + 1 := by simp
  rw [hlen, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
  · rw [List.take_append_of_le_length (le_refl _), List.take_length,
      List.take_of_length_le (by simp)]

theorem ecost_mono {M : Type*} [MetricSpace M]
    (E : EvaderAlgorithm M) (l L : List (Set M)) : E.cost l ≤ E.cost (l ++ L) := by
  induction L using List.reverseRecOn with
  | nil => simp
  | append_singleton L S ih =>
    have h := ecost_concat E (l ++ L) S
    have hd : 0 ≤ dist (E.pos (l ++ L)) (E.pos (l ++ L ++ [S])) := dist_nonneg
    rw [← List.append_assoc]
    linarith

/-- From a chain of `β + 1` points at spacing `u` whose endpoints are `dist`
at least `β * u` apart, the cruel single-file adversary yields a chunk system
with `β` chunks of size `u`. -/
theorem chunkSystem_of_chain {Y : Type} [MetricSpace Y]
    (β : ℕ) (hβ : 1 ≤ β) (u : ℝ) (hu : 0 < u) (pt : ℕ → Y) (s t : Y)
    (hs : pt 0 = s) (ht : pt β = t)
    (hd1 : ∀ i, i < β → dist (pt i) (pt (i + 1)) = u)
    (hd0 : (β : ℝ) * u ≤ dist (pt 0) (pt β))
    (cLo cHi total price : ℝ) (mLo : ℕ)
    (hcLo : cLo ≤ u) (hcHi : u ≤ cHi) (hprice : u ≤ price)
    (hmLo : mLo ≤ β) (htotal : total ≤ (β : ℝ) * u) :
    ∃ C : ChunkSystemB Y s t cLo cHi total price mLo,
      C.m = β ∧ (∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) ∧
      (∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ []) := by
  classical
  subst hs
  subst ht
  set chunkFn : Fin β → List (Set Y) := fun j =>
    if j.val = 0 then [{pt 0}, {pt 1}] else [{pt (j.val + 1)}] with hchunk
  have hstep : ∀ i : ℕ, ∀ _ : i < β,
      ((List.ofFn chunkFn).take (i + 1)).flatten
        = ((List.ofFn chunkFn).take i).flatten
          ++ ((if i = 0 then [{pt 0}] else []) ++ [{pt (i + 1)}]) := by
    intro i hi
    have hlen : i < (List.ofFn chunkFn).length := by simp [hi]
    have htake : (List.ofFn chunkFn).take (i + 1)
        = (List.ofFn chunkFn).take i ++ [(List.ofFn chunkFn).get ⟨i, hlen⟩] := by
      rw [List.take_succ]
      congr 1
      rw [List.getElem?_eq_getElem hlen]
      rfl
    have hget : (List.ofFn chunkFn).get ⟨i, hlen⟩ = chunkFn ⟨i, hi⟩ := by
      simp
    rw [htake, hget, List.flatten_append]
    congr 1
    rw [hchunk]
    by_cases h0 : i = 0
    · simp only [h0]
      rfl
    · have hne0 : (⟨i, hi⟩ : Fin β).val ≠ 0 := h0
      simp only [if_neg hne0, if_neg h0]
      rfl
  have hpin : ∀ (E : EvaderAlgorithm Y) (i : ℕ), ∀ _ : i < β,
      E.pos (((List.ofFn chunkFn).take (i + 1)).flatten) = pt (i + 1) := by
    intro E i hi
    rw [hstep i hi]
    have hne : ({pt (i + 1)} : Set Y).Nonempty := ⟨pt (i + 1), rfl⟩
    have h := E.serves (((List.ofFn chunkFn).take i).flatten
      ++ (if i = 0 then [{pt 0}] else [])) {pt (i + 1)} hne
    rw [← List.append_assoc] at *
    exact h
  have hchunk0 : ∀ j : Fin β, j.val = 0 → chunkFn j = [{pt 0}, {pt 1}] := by
    intro j hj
    rw [hchunk]
    show (if j.val = 0 then [{pt 0}, {pt 1}] else [{pt (j.val + 1)}]) = [{pt 0}, {pt 1}]
    rw [if_pos hj]
  have hchunkN : ∀ j : Fin β, j.val ≠ 0 → chunkFn j = [{pt (j.val + 1)}] := by
    intro j hj
    rw [hchunk]
    show (if j.val = 0 then [{pt 0}, {pt 1}] else [{pt (j.val + 1)}]) = [{pt (j.val + 1)}]
    rw [if_neg hj]
  have hflat : ∀ i : ℕ, 1 ≤ i → i ≤ β →
      ((List.ofFn chunkFn).take i).flatten
        = List.map (fun n => ({pt n} : Set Y)) (List.range (i + 1)) := by
    intro i
    induction i with
    | zero => intro h; omega
    | succ i ih =>
      intro _ hle
      by_cases hi0 : i = 0
      · subst hi0
        have h := hstep 0 (by omega)
        rw [h]
        simp
        rfl
      · have hi1 : 1 ≤ i := by omega
        have h := hstep i (by omega)
        rw [h, ih hi1 (by omega), if_neg hi0]
        rw [List.range_succ (n := i + 1), List.map_append]
        simp
  have hfull : (List.ofFn chunkFn).flatten
      = List.map (fun n => ({pt n} : Set Y)) (List.range (β + 1)) := by
    have h := hflat β hβ (le_refl β)
    rw [List.take_of_length_le (by simp)] at h
    exact h
  have hlen : ((List.ofFn chunkFn).flatten).length = β + 1 := by
    rw [hfull]; simp
  refine ⟨⟨Unit, fun _ => 1, β, fun _ _ => 0, fun _ => chunkFn, fun _ _ => u,
    fun _ => one_pos, by simp, hmLo, by omega, fun _ _ _ _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, fun _ _ => rfl, ?_⟩
  · -- nonemptiness of requests
    intro _ i S hS
    have hS' : S ∈ chunkFn i := hS
    by_cases h0 : i.val = 0
    · rw [hchunk0 i h0] at hS'
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hS'
      rcases hS' with h | h
      · exact h ▸ ⟨pt 0, rfl⟩
      · exact h ▸ ⟨pt 1, rfl⟩
    · rw [hchunkN i h0] at hS'
      rw [List.mem_singleton] at hS'
      exact hS' ▸ ⟨pt (i.val + 1), rfl⟩
  · -- last request is `{t}`
    intro _
    have h2 : (List.ofFn chunkFn).flatten
        = List.map (fun n => ({pt n} : Set Y)) (List.range β) ++ [{pt β}] := by
      rw [hfull, List.range_succ, List.map_append]
      rfl
    rw [h2, List.getLast?_concat]
  · -- the offline optimum
    intro _
    have hQfeas : EvaderServes (pt 0) ((List.ofFn chunkFn).flatten)
        (fun j => if j = 0 then pt 0 else pt (j - 1)) := by
      constructor
      · simp
      · intro j _
        have hget : ((List.ofFn chunkFn).flatten).get j = {pt (j : ℕ)} := by
          have hj' : (j : ℕ) < ((List.ofFn chunkFn).flatten).length := j.2
          have h2 := List.getElem_of_eq hfull hj'
          rw [List.get_eq_getElem, h2, List.getElem_map, List.getElem_range]
        rw [hget]
        simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero _)]
        rfl
    have hmem : (∑ j ∈ Finset.range ((List.ofFn chunkFn).flatten).length,
        dist ((fun j => if j = 0 then pt 0 else pt (j - 1)) j)
          ((fun j => if j = 0 then pt 0 else pt (j - 1)) (j + 1)))
        ∈ {c : ℝ | ∃ Q : ℕ → Y,
            EvaderServes (pt 0) ((List.ofFn chunkFn).flatten) Q ∧
            c = ∑ j ∈ Finset.range ((List.ofFn chunkFn).flatten).length,
              dist (Q j) (Q (j + 1))} := ⟨_, hQfeas, rfl⟩
    have hbdd : BddBelow {c : ℝ | ∃ Q : ℕ → Y,
        EvaderServes (pt 0) ((List.ofFn chunkFn).flatten) Q ∧
        c = ∑ j ∈ Finset.range ((List.ofFn chunkFn).flatten).length,
          dist (Q j) (Q (j + 1))} := by
      refine ⟨0, ?_⟩
      rintro c ⟨Q, -, rfl⟩
      exact Finset.sum_nonneg fun j _ => dist_nonneg
    have hval : (∑ j ∈ Finset.range ((List.ofFn chunkFn).flatten).length,
        dist ((fun j => if j = 0 then pt 0 else pt (j - 1)) j)
          ((fun j => if j = 0 then pt 0 else pt (j - 1)) (j + 1))) = (β : ℝ) * u := by
      rw [hlen, Finset.sum_range_succ']
      have h0 : dist ((fun j => if j = 0 then pt 0 else pt (j - 1)) 0)
          ((fun j => if j = 0 then pt 0 else pt (j - 1)) 1) = 0 := by
        show dist (pt 0) (pt (1 - 1)) = 0
        simp
      have h1 : ∀ i ∈ Finset.range β,
          dist ((fun j => if j = 0 then pt 0 else pt (j - 1)) (i + 1))
            ((fun j => if j = 0 then pt 0 else pt (j - 1)) (i + 1 + 1)) = u := by
        intro i hi
        simp only [Finset.mem_range] at hi
        simp only [if_neg (Nat.succ_ne_zero _)]
        have e1 : i + 1 - 1 = i := by omega
        have e2 : i + 1 + 1 - 1 = i + 1 := by omega
        rw [e1, e2]
        exact hd1 i hi
      rw [Finset.sum_congr rfl h1, h0]
      simp [mul_comm]
    calc evaderOfflineCost (pt 0) ((List.ofFn chunkFn).flatten)
        ≤ _ := csInf_le hbdd hmem
      _ = (β : ℝ) * u := hval
      _ ≤ dist (pt 0) (pt β) := hd0
  · -- the size window
    intro _ _
    exact ⟨hcLo, hcHi⟩
  · -- the conditional cost bound
    intro i ω₀ E bail
    have hfilter : (Finset.univ.filter fun ω : Unit =>
        (fun _ _ => (0 : ℕ)) i.val ω = (fun _ _ => (0 : ℕ)) i.val ω₀) = Finset.univ := by
      refine Finset.filter_true_of_mem ?_
      intro ω _
      rfl
    rw [hfilter]
    have hsum1 : (∑ ω : Unit, (fun _ : Unit => (1 : ℝ)) ω) = 1 := by simp
    have hgoal : u ≤ E.bailCost bail (((List.ofFn chunkFn).take i.val).flatten)
        (chunkFn i) price := by
      refine le_trans ?_ (escapeCost_le_bailCost E bail _ _ _)
      unfold EvaderAlgorithm.escapeCost
      refine Finset.le_inf' _ _ ?_
      intro q hq
      simp only [Finset.mem_range] at hq
      set h : List (Set Y) := ((List.ofFn chunkFn).take i.val).flatten with hh
      have hcost0 : E.costOn h [] = 0 := by
        unfold EvaderAlgorithm.costOn
        rw [List.append_nil]
        ring
      have hcostnn : ∀ L, 0 ≤ E.costOn h L := by
        intro L
        unfold EvaderAlgorithm.costOn
        have := ecost_mono E h L
        linarith
      by_cases hi0 : i.val = 0
      · have hc : chunkFn i = [{pt 0}, {pt 1}] := hchunk0 i hi0
        rw [hc] at hq ⊢
        have hlen2 : ([({pt 0} : Set Y), {pt 1}]).length = 2 := rfl
        rw [hlen2] at hq ⊢
        interval_cases q
        · rw [if_neg (by norm_num)]
          rw [List.take_zero, hcost0]
          linarith
        · rw [if_neg (by norm_num)]
          have := hcostnn ([({pt 0} : Set Y), {pt 1}].take 1)
          linarith
        · rw [if_pos rfl]
          have hhe : h = [] := by
            rw [hh, hi0]
            rfl
          have hsplit : ([({pt 0} : Set Y), {pt 1}])
              = [({pt 0} : Set Y)] ++ [{pt 1}] := rfl
          have hc1 : E.cost ([({pt 0} : Set Y)] ++ [{pt 1}])
              = E.cost [({pt 0} : Set Y)]
                + dist (E.pos [({pt 0} : Set Y)])
                  (E.pos ([({pt 0} : Set Y)] ++ [{pt 1}])) :=
            ecost_concat E _ _
          have hp0 : E.pos [({pt 0} : Set Y)] = pt 0 := by
            have := E.serves [] {pt 0} ⟨pt 0, rfl⟩
            simpa using this
          have hp1 : E.pos ([({pt 0} : Set Y)] ++ [{pt 1}]) = pt 1 := by
            have := E.serves [({pt 0} : Set Y)] {pt 1} ⟨pt 1, rfl⟩
            simpa using this
          have hcost1 : 0 ≤ E.cost [({pt 0} : Set Y)] := by
            have := ecost_mono E [] [({pt 0} : Set Y)]
            unfold EvaderAlgorithm.cost at this ⊢
            simpa using this
          unfold EvaderAlgorithm.costOn
          rw [hhe, List.nil_append, hsplit, hc1, hp0, hp1, hd1 0 (by omega)]
          have hcnil : E.cost ([] : List (Set Y)) = 0 := by
            unfold EvaderAlgorithm.cost
            simp
          rw [hcnil]
          linarith
      · have hc : chunkFn i = [{pt (i.val + 1)}] := hchunkN i hi0
        rw [hc] at hq ⊢
        have hlen1 : ([({pt (i.val + 1)} : Set Y)]).length = 1 := rfl
        rw [hlen1] at hq ⊢
        interval_cases q
        · rw [if_neg (by norm_num)]
          rw [List.take_zero, hcost0]
          linarith
        · rw [if_pos rfl]
          obtain ⟨i', hi'⟩ : ∃ i', i.val = i' + 1 := ⟨i.val - 1, by omega⟩
          have hpos : E.pos h = pt i.val := by
            rw [hh, hi']
            exact hpin E i' (by omega)
          have hcc : E.cost (h ++ [({pt (i.val + 1)} : Set Y)])
              = E.cost h + dist (E.pos h)
                (E.pos (h ++ [({pt (i.val + 1)} : Set Y)])) := ecost_concat E _ _
          have hp1 : E.pos (h ++ [({pt (i.val + 1)} : Set Y)]) = pt (i.val + 1) := by
            have := E.serves h {pt (i.val + 1)} ⟨pt (i.val + 1), rfl⟩
            simpa using this
          unfold EvaderAlgorithm.costOn
          rw [hcc, hpos, hp1, hd1 i.val i.2]
          linarith
    calc u * (∑ ω : Unit, (fun _ : Unit => (1 : ℝ)) ω)
        = u := by rw [hsum1]; ring
      _ ≤ E.bailCost bail (((List.ofFn chunkFn).take i.val).flatten) (chunkFn i) price :=
          hgoal
      _ = ∑ ω : Unit, (fun _ : Unit => (1 : ℝ)) ω
            * E.bailCost bail (((List.ofFn ((fun _ => chunkFn) ω)).take i.val).flatten)
              ((fun _ => chunkFn) ω i) price := by
          simp
  · -- the expected total size
    have hsum : (∑ ω : Unit, (fun _ : Unit => (1 : ℝ)) ω * (∑ _i : Fin β, u))
        = (β : ℝ) * u := by
      simp [mul_comm]
    rw [hsum]
    exact htotal
  · -- every chunk is a nonempty list of requests
    intro _ i
    show chunkFn i ≠ []
    by_cases h0 : i.val = 0
    · rw [hchunk0 i h0]
      simp
    · rw [hchunkN i h0]
      simp

end BCRBase

/-- BCR 2023, Lemma 12, base case at the tight escape price: when `α w² ≤ 1` the
required chunk system on level `w` of the BCR family is the cruel single-file
adversary along the geodesic chain of the level. -/
theorem solution (α : ℝ) (hα : 0 ≤ α)
    (β : ℕ) (hβ : 0 < β) (hβ2 : 2 ≤ β) (w : ℕ) (hw : α * (w : ℝ) ^ 2 ≤ 1) :
    KServer.BCRInductiveChunksTight α β hβ w := by
  classical
  obtain ⟨g, hg0, hgN, hgd⟩ := BCRBase.geo_bcrLevel2 β hβ w
  have hu0 : (0 : ℝ) < (3 : ℝ) ^ w := by positivity
  have hptle : ∀ i : ℕ, i ≤ β → min i β * 3 ^ w ≤ β * 3 ^ w := by
    intro i hi
    exact Nat.mul_le_mul_right _ (by omega)
  have hptcast : ∀ i : ℕ, i ≤ β → ((min i β * 3 ^ w : ℕ) : ℝ) = (i : ℝ) * (3 : ℝ) ^ w := by
    intro i hi
    rw [show min i β = i by omega]
    push_cast
    ring
  have hpt0 : g (min 0 β * 3 ^ w) = (bcrLevel2 β hβ w).s := by simpa using hg0
  have hptβ : g (min β β * 3 ^ w) = (bcrLevel2 β hβ w).t := by simpa using hgN
  have hd1 : ∀ i, i < β →
      dist (g (min i β * 3 ^ w)) (g (min (i + 1) β * 3 ^ w)) = (3 : ℝ) ^ w := by
    intro i hi
    rw [hgd _ (hptle i (by omega)) _ (hptle (i + 1) (by omega)),
      hptcast i (by omega), hptcast (i + 1) (by omega)]
    push_cast
    rw [abs_of_nonpos (by nlinarith)]
    ring
  have hd0 : (β : ℝ) * (3 : ℝ) ^ w
      ≤ dist (g (min 0 β * 3 ^ w)) (g (min β β * 3 ^ w)) := by
    rw [hgd _ (hptle 0 (by omega)) _ (hptle β (le_refl β)),
      hptcast 0 (by omega), hptcast β (le_refl β)]
    push_cast
    rw [abs_of_nonpos (by nlinarith)]
    linarith
  have hβ1 : 1 ≤ β := hβ
  have hβR : (1 : ℝ) ≤ (β : ℝ) := by exact_mod_cast hβ1
  have h1 : α * (β : ℝ) * (w : ℝ) ^ 2 ≤ (β : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) β]
  have hmLo : ⌈α * β * (w : ℝ) ^ 2⌉₊ ≤ β := by
    calc ⌈α * β * (w : ℝ) ^ 2⌉₊ ≤ ⌈(β : ℝ)⌉₊ := Nat.ceil_le_ceil h1
      _ = β := Nat.ceil_natCast β
  obtain ⟨C, hm, h0, hne⟩ := BCRBase.chunkSystem_of_chain
    (Y := (bcrLevel2 β hβ w).carrier) β hβ1
    ((3 : ℝ) ^ w) hu0 (fun i => g (min i β * 3 ^ w))
    (bcrLevel2 β hβ w).s (bcrLevel2 β hβ w).t hpt0 hptβ hd1 hd0
    ((3 : ℝ) ^ w / 2) (3 * (3 : ℝ) ^ w / 2) ((α * β * (w : ℝ) ^ 2) * 3 ^ w)
    ((β : ℝ) * (3 : ℝ) ^ w) β
    (by linarith) (by linarith) (by nlinarith) (le_refl β)
    (mul_le_mul_of_nonneg_right h1 hu0.le)
  exact ⟨β, C, hm, hmLo, h0, hne⟩
