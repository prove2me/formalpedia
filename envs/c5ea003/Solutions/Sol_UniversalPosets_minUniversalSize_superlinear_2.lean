-- Prove2me | solution 2 for UniversalPosets.minUniversalSize_superlinear
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T22:50:00.756176+00:00
-- url     : https://prove2.me/submissions/b0ab7a01-7aca-4aab-9ce7-6ecdfc3570b5

import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_ChainFamily
import Definitions.Def_Cryptography_UniversalPosets_ExactSmall
import Definitions.Def_Cryptography_UniversalPosets_MinSize
import Definitions.Def_Cryptography_UniversalPosets_ThreePosetBound

set_option maxHeartbeats 1000000 in
open Finset UniversalPosets in
theorem solution (C m : ℕ) :
    ∃ n, m ≤ n ∧ C * n ≤ minUniversalSize n := by
  classical
  -- ==== UniversalPosets lemmas, proved from the definitions ====
  have host : ∀ n : ℕ, IsUniversalPosetOfSize (2 ^ n) n := by
    intro n
    classical
    have hcard : Fintype.card (Finset (Fin n)) = 2 ^ n := by simp
    set e : Finset (Fin n) ≃ Fin (2 ^ n) := Fintype.equivFinOfCardEq hcard with hedef
    refine ⟨fun a b => (e.symm a) ⊆ (e.symm b), ?_, ?_⟩
    · refine { refl := ?_, trans := ?_, antisymm := ?_ }
      · intro a; exact Finset.Subset.refl _
      · intro a b c hab hbc; exact Finset.Subset.trans hab hbc
      · intro a b hab hba
        have : e.symm a = e.symm b := Finset.Subset.antisymm hab hba
        exact e.symm.injective this
    · intro r hr
      haveI := hr
      refine ⟨fun x => e ((univ : Finset (Fin n)).filter (fun z => r z x)), ?_⟩
      intro x y
      simp only [Equiv.symm_apply_apply]
      constructor
      · intro hsub
        have hx : x ∈ (univ : Finset (Fin n)).filter (fun z => r z x) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact refl_of r x
        have := hsub hx
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using this
      · intro hxy z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        exact trans_of r hz hxy
  -- an `m`-universal host is `n`-universal for every `n ≤ m`
  have restrict : ∀ {N n m : ℕ}, n ≤ m → IsUniversalPosetOfSize N m →
      IsUniversalPosetOfSize N n := by
    intro N n m hnm h
    obtain ⟨H, hH, huniv⟩ := h
    refine ⟨H, hH, ?_⟩
    intro r hr
    haveI := hr
    set i : Fin n → Fin m := fun x => ⟨(x : ℕ), lt_of_lt_of_le x.isLt hnm⟩ with hidef
    have hinj : Function.Injective i := by
      intro a b hab
      apply Fin.ext
      simpa [hidef, Fin.ext_iff] using hab
    set r' : Fin m → Fin m → Prop :=
      fun a b => a = b ∨ ∃ (ha : (a : ℕ) < n) (hb : (b : ℕ) < n), r ⟨a, ha⟩ ⟨b, hb⟩ with hr'def
    have hr'po : IsPartialOrder (Fin m) r' := by
      refine { refl := ?_, trans := ?_, antisymm := ?_ }
      · intro a; exact Or.inl rfl
      · rintro a b c (rfl | ⟨ha, hb, hab⟩) hbc
        · exact hbc
        · rcases hbc with rfl | ⟨hb2, hc, hbc⟩
          · exact Or.inr ⟨ha, hb, hab⟩
          · refine Or.inr ⟨ha, hc, ?_⟩
            have : (⟨b, hb⟩ : Fin n) = ⟨b, hb2⟩ := rfl
            exact trans_of r hab (this ▸ hbc)
      · rintro a b (rfl | ⟨ha, hb, hab⟩) hba
        · rfl
        · rcases hba with rfl | ⟨hb2, ha2, hba⟩
          · rfl
          · have hx : (⟨a, ha⟩ : Fin n) = ⟨b, hb⟩ := by
              refine antisymm_of r hab ?_
              have e1 : (⟨b, hb2⟩ : Fin n) = ⟨b, hb⟩ := rfl
              have e2 : (⟨a, ha2⟩ : Fin n) = ⟨a, ha⟩ := rfl
              exact e1 ▸ e2 ▸ hba
            exact Fin.ext (by simpa [Fin.ext_iff] using hx)
    obtain ⟨f, hf⟩ := huniv r' hr'po
    refine ⟨fun x => f (i x), ?_⟩
    intro x y
    rw [hf]
    constructor
    · rintro (heq | ⟨ha, hb, hab⟩)
      · have : x = y := hinj heq
        subst this
        exact refl_of r x
      · exact hab
    · intro hxy
      exact Or.inr ⟨x.isLt, y.isLt, hxy⟩
  have isUniversalPosetOfSize_minUniversalSize : ∀ n : ℕ,
      IsUniversalPosetOfSize (minUniversalSize n) n := by
    intro n
    have hne : ({N | IsUniversalPosetOfSize N n} : Set ℕ).Nonempty := ⟨2 ^ n, host n⟩
    have hmem := Nat.sInf_mem hne
    unfold minUniversalSize
    exact hmem
  have minUniversalSize_mono : Monotone minUniversalSize := by
    intro n m hnm
    have hnem : ({N | IsUniversalPosetOfSize N m} : Set ℕ).Nonempty := ⟨2 ^ m, host m⟩
    have hm : IsUniversalPosetOfSize (minUniversalSize m) m := by
      have hmem := Nat.sInf_mem hnem
      unfold minUniversalSize
      exact hmem
    have hmem2 : minUniversalSize m ∈ {N | IsUniversalPosetOfSize N n} := restrict hnm hm
    unfold minUniversalSize
    exact Nat.sInf_le hmem2
  have commonInducedBound_blockChains : ∀ (n d e : ℕ), 0 < d →
      CommonInducedBound (blockChains n e) (blockChains n d) (((n - 1) / e + 1) * d) := by
    intro n d e hd
    classical
    intro A φ hinj hiso
    -- a `d`-block of `Fin n` has at most `d` elements
    have hblock : ∀ c : ℕ, ((univ : Finset (Fin n)).filter
        (fun z : Fin n => (z : ℕ) / d = c)).card ≤ d := by
      intro c
      have hmap : ∀ z ∈ (univ : Finset (Fin n)).filter (fun z : Fin n => (z : ℕ) / d = c),
          (z : ℕ) % d ∈ range d := by
        intro z _
        exact Finset.mem_range.mpr (Nat.mod_lt _ hd)
      have hinj2 : ∀ x ∈ (univ : Finset (Fin n)).filter (fun z : Fin n => (z : ℕ) / d = c),
          ∀ y ∈ (univ : Finset (Fin n)).filter (fun z : Fin n => (z : ℕ) / d = c),
          (x : ℕ) % d = (y : ℕ) % d → x = y := by
        intro x hx y hy hxy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
        refine Fin.ext ?_
        have hx' : (x : ℕ) = d * ((x : ℕ) / d) + (x : ℕ) % d := (Nat.div_add_mod _ _).symm
        have hy' : (y : ℕ) = d * ((y : ℕ) / d) + (y : ℕ) % d := (Nat.div_add_mod _ _).symm
        rw [hx] at hx'
        rw [hy] at hy'
        omega
      have := Finset.card_le_card_of_injOn (fun z : Fin n => (z : ℕ) % d) hmap
        (fun x hx y hy h => hinj2 x hx y hy h)
      simpa using this
    -- every `e`-block of `A` lands inside one `d`-block, injectively
    have hfib : ∀ c ∈ A.image (fun x : Fin n => (x : ℕ) / e),
        (A.filter (fun x : Fin n => (x : ℕ) / e = c)).card ≤ d := by
      intro c _
      rcases Finset.eq_empty_or_nonempty (A.filter (fun x : Fin n => (x : ℕ) / e = c)) with
        hemp | ⟨x0, hx0⟩
      · rw [hemp]; simp
      · have hx0A : x0 ∈ A := (Finset.mem_filter.mp hx0).1
        have hx0c : (x0 : ℕ) / e = c := (Finset.mem_filter.mp hx0).2
        have hsame : ∀ x ∈ A.filter (fun x : Fin n => (x : ℕ) / e = c),
            (φ x : ℕ) / d = (φ x0 : ℕ) / d := by
          intro x hx
          have hxA : x ∈ A := (Finset.mem_filter.mp hx).1
          have hxc : (x : ℕ) / e = c := (Finset.mem_filter.mp hx).2
          rcases le_total x x0 with hle | hle
          · have := (hiso x hxA x0 hx0A).mp ⟨hle, by rw [hxc, hx0c]⟩
            exact this.2
          · have := (hiso x0 hx0A x hxA).mp ⟨hle, by rw [hxc, hx0c]⟩
            exact this.2.symm
        have hsub : ∀ x ∈ A.filter (fun x : Fin n => (x : ℕ) / e = c),
            φ x ∈ (univ : Finset (Fin n)).filter
              (fun z : Fin n => (z : ℕ) / d = (φ x0 : ℕ) / d) := by
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hsame x hx
        have hcard := Finset.card_le_card_of_injOn φ hsub
          (fun x hx y hy h => hinj (Finset.mem_coe.mpr (Finset.mem_filter.mp hx).1)
            (Finset.mem_coe.mpr (Finset.mem_filter.mp hy).1) h)
        exact le_trans hcard (hblock _)
    have h1 : A.card ≤ d * (A.image (fun x : Fin n => (x : ℕ) / e)).card :=
      Finset.card_le_mul_card_image _ _ hfib
    have h2 : (A.image (fun x : Fin n => (x : ℕ) / e)).card ≤ (n - 1) / e + 1 := by
      have hsub : A.image (fun x : Fin n => (x : ℕ) / e) ⊆ range ((n - 1) / e + 1) := by
        intro c hc
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hc
        refine Finset.mem_range.mpr ?_
        have hxn : (x : ℕ) ≤ n - 1 := by omega
        exact Nat.lt_succ_of_le (Nat.div_le_div_right hxn)
      simpa using Finset.card_le_card hsub
    calc A.card ≤ d * (A.image (fun x : Fin n => (x : ℕ) / e)).card := h1
      _ ≤ d * ((n - 1) / e + 1) := by exact Nat.mul_le_mul_left d h2
      _ = ((n - 1) / e + 1) * d := by ring
  have family_lower_bound : ∀ {N n k : ℕ}, IsUniversalPosetOfSize N n →
      ∀ (r : ℕ → Fin n → Fin n → Prop), (∀ i, IsPartialOrder (Fin n) (r i)) →
      ∀ (s : ℕ → ℕ → ℕ), (∀ i j, j < i → CommonInducedBound (r i) (r j) (s i j)) →
      k * n ≤ N + ∑ i ∈ range k, ∑ j ∈ range i, s i j := by
    intro N n k h r hr s hs
    classical
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨H, hH, huniv⟩ := h
    haveI := hH
    choose f hf using fun i => huniv (r i) (hr i)
    have hfinj : ∀ i, Function.Injective (f i) := by
      intro i x y hxy
      haveI := hr i
      have h1 : r i x y := (hf i x y).mp (by rw [hxy]; exact refl_of H (f i y))
      have h2 : r i y x := (hf i y x).mp (by rw [hxy]; exact refl_of H (f i y))
      exact antisymm_of (r i) h1 h2
    set A : ℕ → Finset (Pt N) := fun i => (univ : Finset (Fin n)).image (f i) with hAdef
    have hcardA : ∀ i, (A i).card = n := by
      intro i
      rw [hAdef, Finset.card_image_of_injective _ (hfinj i), Finset.card_univ, Fintype.card_fin]
    have hinter : ∀ i j, j < i → (A i ∩ A j).card ≤ s i j := by
      intro i j hji
      set B := (univ : Finset (Fin n)).filter (fun x => f i x ∈ A j) with hBdef
      have hBimg : A i ∩ A j = B.image (f i) := by
        ext z
        simp only [hAdef, hBdef, Finset.mem_inter, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨x, rfl⟩, hz⟩; exact ⟨x, hz, rfl⟩
        · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, rfl⟩, hx⟩
      have hBcard : (A i ∩ A j).card = B.card := by
        rw [hBimg, Finset.card_image_of_injective _ (hfinj i)]
      set φ : Fin n → Fin n := fun x => Function.invFun (f j) (f i x) with hφdef
      have hφ : ∀ x ∈ B, f j (φ x) = f i x := by
        intro x hx
        simp only [hBdef, hAdef, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hx
        exact Function.invFun_eq ⟨y, hy⟩
      have hinjOn : Set.InjOn φ ↑B := by
        intro x hx y hy hxy
        have e1 := hφ x (Finset.mem_coe.mp hx)
        have e2 := hφ y (Finset.mem_coe.mp hy)
        apply hfinj i
        rw [← e1, ← e2, hxy]
      have hiso : ∀ x ∈ B, ∀ y ∈ B, (r i x y ↔ r j (φ x) (φ y)) := by
        intro x hx y hy
        rw [← hf i x y, ← hf j (φ x) (φ y), hφ x hx, hφ y hy]
      have := hs i j hji B φ hinjOn hiso
      omega
    have bonf : ∑ i ∈ range k, (A i).card
        ≤ ((range k).biUnion A).card + ∑ i ∈ range k, ∑ j ∈ range i, (A i ∩ A j).card := by
      clear hinter hcardA
      induction k with
      | zero => simp
      | succ K ih =>
          have hins : range (K + 1) = insert K (range K) := by
            ext z; simp only [Finset.mem_insert, Finset.mem_range]; omega
          have hU : ((range (K + 1)).biUnion A) = A K ∪ (range K).biUnion A := by
            rw [hins, Finset.biUnion_insert]
          have hcap : (A K ∩ (range K).biUnion A).card ≤ ∑ j ∈ range K, (A K ∩ A j).card := by
            have hEq : A K ∩ (range K).biUnion A = (range K).biUnion (fun j => A K ∩ A j) := by
              ext z
              simp only [Finset.mem_inter, Finset.mem_biUnion]
              constructor
              · rintro ⟨hz, j, hj, hzj⟩; exact ⟨j, hj, hz, hzj⟩
              · rintro ⟨j, hj, hz, hzj⟩; exact ⟨hz, j, hj, hzj⟩
            rw [hEq]
            exact Finset.card_biUnion_le
          have hunion := Finset.card_union_add_card_inter (A K) ((range K).biUnion A)
          rw [Finset.sum_range_succ, Finset.sum_range_succ, hU]
          omega
    have hhost : ((range k).biUnion A).card ≤ N := by
      have h1 := Finset.card_le_univ ((range k).biUnion A)
      have h2 : Fintype.card (Pt N) = N := by
        first
          | rfl
          | (show Fintype.card (Fin N) = N; exact Fintype.card_fin N)
          | simp [Pt]
      omega
    have hsum : ∑ i ∈ range k, ∑ j ∈ range i, (A i ∩ A j).card
        ≤ ∑ i ∈ range k, ∑ j ∈ range i, s i j := by
      refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
      exact hinter i j (Finset.mem_range.mp hj)
    have hleft : ∑ i ∈ range k, (A i).card = k * n := by
      rw [Finset.sum_congr rfl (fun i _ => hcardA i), Finset.sum_const, Finset.card_range,
        smul_eq_mul]
    omega
  -- ==== end of inlined lemmas ====
  have hlog6 : ∀ n : ℕ, Nat.log 4 n * n ≤ 6 * minUniversalSize n := by
    intro n
    have hcore : ∀ k : ℕ, 2 * (k * 4 ^ k) ≤ 3 * minUniversalSize (4 ^ k) := by
      intro k
      set m : ℕ := 4 ^ k with hm
      set M : ℕ := minUniversalSize m with hM
      -- the block-chain family is a family of partial orders
      have hpo : ∀ d : ℕ, IsPartialOrder (Fin m) (blockChains m d) := by
        intro d
        haveI hr : IsRefl (Fin m) (blockChains m d) := ⟨fun a => ⟨le_refl a, rfl⟩⟩
        haveI ht : IsTrans (Fin m) (blockChains m d) := by
          refine ⟨fun a b c hab hbc => ?_⟩
          exact ⟨le_trans hab.1 hbc.1, hab.2.trans hbc.2⟩
        haveI ha : IsAntisymm (Fin m) (blockChains m d) := by
          refine ⟨fun a b hab hba => ?_⟩
          exact le_antisymm hab.1 hba.1
        haveI hp : IsPreorder (Fin m) (blockChains m d) := ⟨⟩
        exact ⟨⟩
      -- the family lower bound, with `r i` the blocks of length `4 ^ i`
      have hmain := family_lower_bound (N := M) (n := m) (k := k)
        (isUniversalPosetOfSize_minUniversalSize m)
        (fun i => blockChains m (4 ^ i)) (fun i => hpo (4 ^ i))
        (fun i j => ((m - 1) / 4 ^ i + 1) * 4 ^ j)
        (fun i j _ => commonInducedBound_blockChains m (4 ^ j) (4 ^ i) (by positivity))
      -- the exact value of the truncated quotient
      have hdiv : ∀ i : ℕ, i < k → (m - 1) / 4 ^ i + 1 = 4 ^ (k - i) := by
        intro i hik
        have hsplit : (4 : ℕ) ^ (k - i) * 4 ^ i = m := by
          rw [hm, ← pow_add]
          congr 1
          omega
        have hpos : 0 < (4 : ℕ) ^ i := by positivity
        have hq : (m - 1) / 4 ^ i = 4 ^ (k - i) - 1 := by
          refine Nat.div_eq_of_lt_le ?_ ?_
          · have hexp : ((4 : ℕ) ^ (k - i) - 1) * 4 ^ i = m - 4 ^ i := by
              rw [Nat.sub_mul, one_mul, hsplit]
            rw [hexp]
            omega
          · have h2 : (4 : ℕ) ^ (k - i) - 1 + 1 = 4 ^ (k - i) := by
              have : 0 < (4 : ℕ) ^ (k - i) := by positivity
              omega
            rw [h2, hsplit]
            have : 0 < m := by rw [hm]; positivity
            omega
        have hge : 0 < (4 : ℕ) ^ (k - i) := by positivity
        rw [hq]
        omega
      -- bound the double sum
      have hgeom : ∀ i : ℕ, 3 * (∑ j ∈ range i, (4 : ℕ) ^ j) + 1 = 4 ^ i := by
        intro i
        induction i with
        | zero => simp
        | succ m ih =>
          rw [Finset.sum_range_succ, pow_succ]
          omega
      have hrow : ∀ i ∈ range k,
          3 * (∑ j ∈ range i, ((m - 1) / 4 ^ i + 1) * 4 ^ j) + 4 ^ (k - i) = m := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [hdiv i hi, ← Finset.mul_sum]
        have hg := hgeom i
        have hsplit : (4 : ℕ) ^ (k - i) * 4 ^ i = m := by
          rw [hm, ← pow_add]
          congr 1
          omega
        calc 3 * (4 ^ (k - i) * ∑ j ∈ range i, (4 : ℕ) ^ j) + 4 ^ (k - i)
            = 4 ^ (k - i) * (3 * (∑ j ∈ range i, (4 : ℕ) ^ j) + 1) := by ring
          _ = 4 ^ (k - i) * 4 ^ i := by rw [hg]
          _ = m := hsplit
      have hsum : 3 * (∑ i ∈ range k, ∑ j ∈ range i, ((m - 1) / 4 ^ i + 1) * 4 ^ j) + k ≤ k * m := by
        have hle : ∀ i ∈ range k,
            3 * (∑ j ∈ range i, ((m - 1) / 4 ^ i + 1) * 4 ^ j) + 1 ≤ m := by
          intro i hi
          have h := hrow i hi
          have hge : 1 ≤ (4 : ℕ) ^ (k - i) := Nat.one_le_pow _ _ (by norm_num)
          omega
        have hexp : ∑ i ∈ range k, (3 * (∑ j ∈ range i, ((m - 1) / 4 ^ i + 1) * 4 ^ j) + 1)
            = 3 * (∑ i ∈ range k, ∑ j ∈ range i, ((m - 1) / 4 ^ i + 1) * 4 ^ j) + k := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
            smul_eq_mul, mul_one]
        calc 3 * (∑ i ∈ range k, ∑ j ∈ range i, ((m - 1) / 4 ^ i + 1) * 4 ^ j) + k
            = ∑ i ∈ range k, (3 * (∑ j ∈ range i, ((m - 1) / 4 ^ i + 1) * 4 ^ j) + 1) := hexp.symm
          _ ≤ ∑ _i ∈ range k, m := Finset.sum_le_sum hle
          _ = k * m := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      linarith [hmain, hsum]

    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    set k : ℕ := Nat.log 4 n with hk
    have h4k : 4 ^ k ≤ n := Nat.pow_log_le_self 4 (by omega)
    have hlt : n < 4 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have hmono : minUniversalSize (4 ^ k) ≤ minUniversalSize n := minUniversalSize_mono h4k
    have hc := hcore k
    have hpow : (4 : ℕ) ^ (k + 1) = 4 * 4 ^ k := by ring
    have hn4 : n ≤ 4 * 4 ^ k := by omega
    calc k * n ≤ k * (4 * 4 ^ k) := Nat.mul_le_mul_left k hn4
      _ = 2 * (2 * (k * 4 ^ k)) := by ring
      _ ≤ 2 * (3 * minUniversalSize (4 ^ k)) := by omega
      _ ≤ 6 * minUniversalSize n := by omega

  refine ⟨max m (4 ^ (6 * C)), le_max_left _ _, ?_⟩
  have hpow : (4 : ℕ) ^ (6 * C) ≤ max m (4 ^ (6 * C)) := le_max_right _ _
  have hlogge : 6 * C ≤ Nat.log 4 (max m (4 ^ (6 * C))) :=
    Nat.le_log_of_pow_le (by norm_num) hpow
  have h6 := hlog6 (max m (4 ^ (6 * C)))
  have hstep : 6 * C * max m (4 ^ (6 * C))
      ≤ Nat.log 4 (max m (4 ^ (6 * C))) * max m (4 ^ (6 * C)) :=
    Nat.mul_le_mul_right _ hlogge
  have hmul : 6 * (C * max m (4 ^ (6 * C)))
      ≤ 6 * minUniversalSize (max m (4 ^ (6 * C))) := by
    calc 6 * (C * max m (4 ^ (6 * C))) = 6 * C * max m (4 ^ (6 * C)) := by ring
      _ ≤ Nat.log 4 (max m (4 ^ (6 * C))) * max m (4 ^ (6 * C)) := hstep
      _ ≤ 6 * minUniversalSize (max m (4 ^ (6 * C))) := h6
  exact Nat.le_of_mul_le_mul_left hmul (by norm_num)
