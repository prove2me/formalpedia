-- Prove2me | solution 1 for KServer.offline_avg_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T02:49:33.694982+00:00
-- url     : https://prove2.me/submissions/8d378dc6-84d8-48f6-83c0-d602b4d12797

import Mathlib
import Definitions.Def_KServer_model

open KServer

/-! ### Generic auxiliaries -/

/-- A finite set of cardinality `k` is the injective image of `Fin k`. -/
private theorem exists_bij_of_card {M : Type} [DecidableEq M] {k : ℕ}
    (s : Finset M) (hs : s.card = k) :
    ∃ f : Fin k → M, Function.Injective f ∧ Finset.image f Finset.univ = s := by
  classical
  have hcard : Fintype.card (Fin k) = Fintype.card ↥s := by simp [hs]
  obtain e := Fintype.equivOfCardEq hcard
  refine ⟨fun i => (e i : M), ?_, ?_⟩
  · intro a b hab
    exact e.injective (Subtype.ext hab)
  · ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩; exact (e i).2
    · intro hy; exact ⟨e.symm ⟨y, hy⟩, by simp⟩

/-- Swapping `x` and `y` carries `P \ {y}` onto `P \ {x}`. -/
private theorem image_swap_erase {M : Type} [DecidableEq M] (P : Finset M) (x y : M)
    (hx : x ∈ P) (hy : y ∈ P) :
    Finset.image (Equiv.swap x y) (P.erase y) = P.erase x := by
  ext z
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨w, ⟨hwy, hwP⟩, rfl⟩
    rcases eq_or_ne w x with hwx | hwx
    · subst hwx
      rw [Equiv.swap_apply_left]
      exact ⟨Ne.symm hwy, hy⟩
    · rw [Equiv.swap_apply_of_ne_of_ne hwx hwy]
      exact ⟨hwx, hwP⟩
  · rintro ⟨hzx, hzP⟩
    rcases eq_or_ne z y with rfl | hzy
    · exact ⟨x, ⟨fun h => hzx h.symm, hx⟩, by rw [Equiv.swap_apply_left]⟩
    · exact ⟨z, ⟨hzy, hzP⟩, Equiv.swap_apply_of_ne_of_ne hzx hzy⟩

/-- `moveCost` obeys the triangle inequality. -/
private theorem moveCost_triangle {k : ℕ} {M : Type} [MetricSpace M]
    (A B C : Config k M) : moveCost A C ≤ moveCost A B + moveCost B C := by
  unfold moveCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => dist_triangle _ _ _

private theorem moveCost_nonneg {k : ℕ} {M : Type} [MetricSpace M] (A B : Config k M) :
    0 ≤ moveCost A B := Finset.sum_nonneg fun i _ => dist_nonneg

/-- The consecutive-distance sum of a list, as a sum over indices. -/
private theorem consec_eq_range_sum {M : Type} [MetricSpace M] (d₀ : M) :
    ∀ σ : List M, ((σ.zip σ.tail).map (fun p => dist p.1 p.2)).sum
      = ∑ j ∈ Finset.range (σ.length - 1), dist (σ.getD j d₀) (σ.getD (j + 1) d₀)
  | [] => by simp
  | [_] => by simp
  | a :: b :: t => by
    have ih := consec_eq_range_sum d₀ (b :: t)
    have hz : ((a :: b :: t).zip (a :: b :: t).tail)
        = (a, b) :: ((b :: t).zip (b :: t).tail) := by simp
    have hterm : ∀ x : ℕ,
        dist ((a :: b :: t).getD (x + 1) d₀) ((a :: b :: t).getD (x + 1 + 1) d₀)
          = dist ((b :: t).getD x d₀) ((b :: t).getD (x + 1) d₀) := by
      intro x; simp
    have h0 : (a :: b :: t).getD 0 d₀ = a := by simp
    have h1 : (a :: b :: t).getD 1 d₀ = b := by simp
    have hlen : (a :: b :: t).length - 1 = (b :: t).length - 1 + 1 := by simp
    rw [hz, List.map_cons, List.sum_cons, ih, hlen, Finset.sum_range_succ',
      Finset.sum_congr rfl (fun x (_ : x ∈ Finset.range ((b :: t).length - 1)) => hterm x),
      h0, h1, add_comm]

/-- The permutation carrying the `h`-adversary's servers to their positions after
`j` requests: it swaps only when the request is the adversary's own hole. -/
private def advPerm {M : Type} [DecidableEq M] (req : ℕ → M) (h : M) :
    ℕ → Equiv.Perm M
  | 0 => 1
  | j + 1 =>
      if (advPerm req h j) h = req (j + 1) then
        Equiv.swap (req j) (req (j + 1)) * advPerm req h j
      else advPerm req h j

private theorem advPerm_zero {M : Type} [DecidableEq M] (req : ℕ → M) (h : M) :
    advPerm req h 0 = 1 := rfl

private theorem advPerm_succ {M : Type} [DecidableEq M] (req : ℕ → M) (h : M) (j : ℕ) :
    advPerm req h (j + 1) =
      if (advPerm req h j) h = req (j + 1) then
        Equiv.swap (req j) (req (j + 1)) * advPerm req h j
      else advPerm req h j := rfl

/-! ### The `k` offline algorithms -/

theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (P : Finset M) (hP : P.card = k + 1) (C₀ : Config k M) :
    ∃ D : ℝ, ∀ σ : List M, (∀ r ∈ σ, r ∈ P) →
      (k : ℝ) * offlineCost C₀ σ
        ≤ ((σ.zip σ.tail).map (fun p => dist p.1 p.2)).sum + D := by
  classical
  obtain ⟨q₀, hq₀⟩ : P.Nonempty := Finset.card_pos.mp (by omega)
  set Δ : ℝ := (P ×ˢ P).sup' ⟨(q₀, q₀), Finset.mem_product.mpr ⟨hq₀, hq₀⟩⟩
      (fun z => dist z.1 z.2) with hΔdef
  have hΔ : ∀ p ∈ P, ∀ q ∈ P, dist p q ≤ Δ := by
    intro p hp q hq
    have hpq : (p, q) ∈ P ×ˢ P := Finset.mem_product.mpr ⟨hp, hq⟩
    rw [hΔdef]
    exact Finset.le_sup' (fun z : M × M => dist z.1 z.2) hpq
  have hΔ0 : (0:ℝ) ≤ Δ := by simpa using hΔ q₀ hq₀ q₀ hq₀
  have hcardE : (P.erase q₀).card = k := by
    rw [Finset.card_erase_of_mem hq₀, hP]; omega
  -- one initial configuration per hole
  have hbase : ∀ h : M, ∃ f : Fin k → M,
      h ∈ P → (Function.Injective f ∧ Finset.image f Finset.univ = P.erase h) := by
    intro h
    by_cases hh : h ∈ P
    · obtain ⟨f, h1, h2⟩ := exists_bij_of_card (P.erase h)
        (by rw [Finset.card_erase_of_mem hh, hP])
      exact ⟨f, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => q₀, fun hc => absurd hc hh⟩
  choose base hbase_spec using hbase
  refine ⟨(∑ h ∈ P.erase q₀, moveCost C₀ (base h)) + Δ, ?_⟩
  intro σ hσ
  -- the request stream; `req 0` is the point covered by every offline algorithm
  obtain ⟨req, hreq0, hreqS⟩ : ∃ req : ℕ → M, req 0 = q₀ ∧ ∀ j, req (j + 1) = σ.getD j q₀ :=
    ⟨fun j => match j with | 0 => q₀ | (m + 1) => σ.getD m q₀, rfl, fun _ => rfl⟩
  have hreqP : ∀ j, req j ∈ P := by
    intro j
    cases j with
    | zero => rw [hreq0]; exact hq₀
    | succ m =>
      rw [hreqS]
      by_cases hm : m < σ.length
      · rw [List.getD_eq_getElem σ q₀ hm]; exact hσ _ (List.getElem_mem hm)
      · rw [List.getD_eq_default σ q₀ (by omega)]; exact hq₀
  obtain ⟨S, hS⟩ : ∃ S : M → ℕ → Config k M,
      ∀ h j i, S h j i = advPerm req h j (base h i) := ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨hole, hhole⟩ : ∃ hole : M → ℕ → M,
      ∀ h j, hole h j = advPerm req h j h := ⟨_, fun _ _ => rfl⟩
  have hhole0 : ∀ h, hole h 0 = h := by intro h; simp [hhole, advPerm_zero]
  have hholeS : ∀ h j, hole h (j + 1)
      = if hole h j = req (j + 1) then req j else hole h j := by
    intro h j
    simp only [hhole, advPerm_succ]
    by_cases hc : advPerm req h j h = req (j + 1)
    · simp [hc, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    · simp [hc]
  have hS0 : ∀ h i, S h 0 i = base h i := by intro h i; simp [hS, advPerm_zero]
  have hSS : ∀ h j i, S h (j + 1) i =
      if hole h j = req (j + 1) then Equiv.swap (req j) (req (j + 1)) (S h j i)
      else S h j i := by
    intro h j i
    simp only [hS, hhole, advPerm_succ]
    by_cases hc : advPerm req h j h = req (j + 1)
    · simp [hc, Equiv.Perm.mul_apply]
    · simp [hc]
  -- THE INVARIANT
  have hinv : ∀ j : ℕ,
      Finset.image (fun h => hole h j) (P.erase q₀) = P.erase (req j) ∧
      Set.InjOn (fun h => hole h j) (P.erase q₀) ∧
      (∀ h ∈ P.erase q₀, Finset.image (S h j) Finset.univ = P.erase (hole h j)) ∧
      (∀ h ∈ P.erase q₀, Function.Injective (S h j)) := by
    intro j
    induction j with
    | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hreq0]
        rw [show (fun h => hole h 0) = (fun h => h) from funext hhole0]
        exact Finset.image_id
      · intro a _ b _ hab
        simpa [hhole0] using hab
      · intro h hh
        rw [show S h 0 = base h from funext (hS0 h), hhole0]
        exact (hbase_spec h (Finset.mem_of_mem_erase hh)).2
      · intro h hh
        rw [show S h 0 = base h from funext (hS0 h)]
        exact (hbase_spec h (Finset.mem_of_mem_erase hh)).1
    | succ j ih =>
      obtain ⟨ihimg, ihinj, ihSimg, ihSinj⟩ := ih
      have hsP : req j ∈ P := hreqP j
      have hrP : req (j + 1) ∈ P := hreqP (j + 1)
      -- each hole lies in `P` and differs from the common point
      have hholemem : ∀ h ∈ P.erase q₀, hole h j ∈ P.erase (req j) := by
        intro h hh
        rw [← ihimg]
        exact Finset.mem_image_of_mem _ hh
      -- the hole map is transported by the swap
      have hswap : ∀ h ∈ P.erase q₀,
          hole h (j + 1) = Equiv.swap (req (j + 1)) (req j) (hole h j) := by
        intro h hh
        have hne : hole h j ≠ req j := (Finset.mem_erase.mp (hholemem h hh)).1
        rw [hholeS]
        by_cases hc : hole h j = req (j + 1)
        · rw [if_pos hc, hc, Equiv.swap_apply_left]
        · rw [if_neg hc, Equiv.swap_apply_of_ne_of_ne hc hne]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hrw : Finset.image (fun h => hole h (j + 1)) (P.erase q₀)
            = Finset.image (Equiv.swap (req (j + 1)) (req j))
                (Finset.image (fun h => hole h j) (P.erase q₀)) := by
          rw [Finset.image_image]
          refine Finset.image_congr ?_
          intro h hh
          exact hswap h (Finset.mem_coe.mp hh)
        rw [hrw, ihimg]
        exact image_swap_erase P (req (j + 1)) (req j) hrP hsP
      · intro a ha b hb hab
        have hab' : hole a (j + 1) = hole b (j + 1) := hab
        rw [hswap a (Finset.mem_coe.mp ha), hswap b (Finset.mem_coe.mp hb)] at hab'
        exact ihinj ha hb ((Equiv.swap (req (j + 1)) (req j)).injective hab')
      · intro h hh
        by_cases hc : hole h j = req (j + 1)
        · have hfun : S h (j + 1) = fun i => Equiv.swap (req j) (req (j + 1)) (S h j i) :=
            funext fun i => by rw [hSS, if_pos hc]
          rw [hfun, show (fun i => Equiv.swap (req j) (req (j + 1)) (S h j i))
              = (Equiv.swap (req j) (req (j + 1))) ∘ (S h j) from rfl,
            ← Finset.image_image, ihSimg h hh, hc, hholeS, if_pos hc]
          exact image_swap_erase P (req j) (req (j + 1)) hsP hrP
        · have hfun : S h (j + 1) = S h j := funext fun i => by rw [hSS, if_neg hc]
          rw [hfun, hholeS, if_neg hc]
          exact ihSimg h hh
      · intro h hh
        by_cases hc : hole h j = req (j + 1)
        · have hfun : S h (j + 1) = fun i => Equiv.swap (req j) (req (j + 1)) (S h j i) :=
            funext fun i => by rw [hSS, if_pos hc]
          rw [hfun]
          exact (Equiv.swap (req j) (req (j + 1))).injective.comp (ihSinj h hh)
        · have hfun : S h (j + 1) = S h j := funext fun i => by rw [hSS, if_neg hc]
          rw [hfun]; exact ihSinj h hh
  -- EXACTLY ONE OFFLINE ALGORITHM MOVES, AND IT PAYS THE CONSECUTIVE DISTANCE
  have hstepcost : ∀ j : ℕ,
      ∑ h ∈ P.erase q₀, moveCost (S h j) (S h (j + 1)) = dist (req j) (req (j + 1)) := by
    intro j
    obtain ⟨ihimg, ihinj, ihSimg, ihSinj⟩ := hinv j
    have hnomove : ∀ h ∈ P.erase q₀, hole h j ≠ req (j + 1) →
        moveCost (S h j) (S h (j + 1)) = 0 := by
      intro h _ hc
      have hfun : S h (j + 1) = S h j := funext fun i => by rw [hSS, if_neg hc]
      rw [hfun]
      simp [moveCost]
    by_cases hrs : req (j + 1) = req j
    · rw [hrs, dist_self]
      refine Finset.sum_eq_zero fun h hh => hnomove h hh ?_
      rw [hrs]
      exact (Finset.mem_erase.mp (by rw [← ihimg]; exact Finset.mem_image_of_mem _ hh)).1
    · have hmem : req (j + 1) ∈ P.erase (req j) :=
        Finset.mem_erase.mpr ⟨hrs, hreqP (j + 1)⟩
      obtain ⟨h₀, hh₀mem, hh₀⟩ := Finset.mem_image.mp (ihimg ▸ hmem)
      rw [Finset.sum_eq_single h₀ (fun h hh hne => hnomove h hh (fun hc =>
        hne (ihinj hh hh₀mem (show hole h j = hole h₀ j by rw [hc, hh₀]))))
        (fun hc => absurd hh₀mem hc)]
      -- the mover: one server travels from the common point to the request
      have hfun : S h₀ (j + 1) = fun i => Equiv.swap (req j) (req (j + 1)) (S h₀ j i) :=
        funext fun i => by rw [hSS, if_pos hh₀]
      have hsmem : req j ∈ P.erase (req (j + 1)) :=
        Finset.mem_erase.mpr ⟨fun hc => hrs hc.symm, hreqP j⟩
      obtain ⟨i₀, -, hi₀⟩ := Finset.mem_image.mp
        (by rw [ihSimg h₀ hh₀mem, hh₀]; exact hsmem)
      rw [hfun]
      unfold moveCost
      rw [Finset.sum_eq_single i₀ ?_ (by simp)]
      · show dist (S h₀ j i₀) (Equiv.swap (req j) (req (j + 1)) (S h₀ j i₀))
            = dist (req j) (req (j + 1))
        rw [hi₀, Equiv.swap_apply_left]
      · intro i _ hne
        have h1 : S h₀ j i ≠ req j := fun hc => hne (ihSinj h₀ hh₀mem (hc.trans hi₀.symm))
        have h2 : S h₀ j i ≠ req (j + 1) := by
          intro hc
          have : req (j + 1) ∈ Finset.image (S h₀ j) Finset.univ :=
            hc ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i)
          rw [ihSimg h₀ hh₀mem, hh₀] at this
          exact (Finset.mem_erase.mp this).1 rfl
        show dist (S h₀ j i) (Equiv.swap (req j) (req (j + 1)) (S h₀ j i)) = 0
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2, dist_self]
  -- THE SCHEDULES
  obtain ⟨sched, hsched0, hschedS⟩ : ∃ sched : M → ℕ → Config k M,
      (∀ h, sched h 0 = C₀) ∧ (∀ h j, sched h (j + 1) = S h (j + 1)) :=
    ⟨fun h j => if j = 0 then C₀ else S h j, fun h => by simp, fun h j => by simp⟩
  have hserves : ∀ h ∈ P.erase q₀, ServesFrom C₀ σ (sched h) := by
    intro h hh
    refine ⟨hsched0 h, ?_⟩
    intro j
    obtain ⟨-, -, ihSimg, -⟩ := hinv (j + 1)
    have hgoal : σ.get j = req (j + 1) := by
      rw [hreqS, List.getD_eq_getElem σ q₀ j.2]
      simp
    have hne : req (j + 1) ≠ hole h (j + 1) := by
      obtain ⟨himg, -, -, -⟩ := hinv (j + 1)
      have : hole h (j + 1) ∈ P.erase (req (j + 1)) := by
        rw [← himg]; exact Finset.mem_image_of_mem _ hh
      exact fun hc => (Finset.mem_erase.mp this).1 hc.symm
    have : req (j + 1) ∈ Finset.image (S h (j + 1)) Finset.univ := by
      rw [ihSimg h hh]
      exact Finset.mem_erase.mpr ⟨hne, hreqP (j + 1)⟩
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp this
    exact ⟨i, by rw [hschedS, hi, hgoal]⟩
  have hschedcost : ∀ h ∈ P.erase q₀,
      (∑ j ∈ Finset.range σ.length, moveCost (sched h j) (sched h (j + 1)))
        ≤ moveCost C₀ (base h)
          + ∑ j ∈ Finset.range σ.length, moveCost (S h j) (S h (j + 1)) := by
    intro h _
    cases hn : σ.length with
    | zero => simp [moveCost_nonneg]
    | succ m =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have hb : S h 0 = base h := funext (hS0 h)
      have h1 : moveCost (sched h 0) (sched h (0 + 1))
          ≤ moveCost C₀ (base h) + moveCost (S h 0) (S h (0 + 1)) := by
        rw [hsched0, hschedS, ← hb]
        exact moveCost_triangle _ _ _
      have h2 : ∀ i ∈ Finset.range m, moveCost (sched h (i + 1)) (sched h (i + 1 + 1))
          = moveCost (S h (i + 1)) (S h (i + 1 + 1)) := by
        intro i _; rw [hschedS, hschedS]
      rw [Finset.sum_congr rfl h2]
      linarith [h1]
  -- ASSEMBLY
  have hbdd : BddBelow {c : ℝ | ∃ T : ℕ → Config k M, ServesFrom C₀ σ T ∧
      c = ∑ j ∈ Finset.range σ.length, moveCost (T j) (T (j + 1))} := by
    refine ⟨0, ?_⟩
    rintro c ⟨T, -, rfl⟩
    exact Finset.sum_nonneg fun j _ => moveCost_nonneg _ _
  have hOPTle : ∀ h ∈ P.erase q₀, offlineCost C₀ σ
      ≤ ∑ j ∈ Finset.range σ.length, moveCost (sched h j) (sched h (j + 1)) := by
    intro h hh
    unfold offlineCost
    exact csInf_le hbdd ⟨sched h, hserves h hh, rfl⟩
  have hsum1 : (k : ℝ) * offlineCost C₀ σ
      ≤ ∑ h ∈ P.erase q₀, ∑ j ∈ Finset.range σ.length,
          moveCost (sched h j) (sched h (j + 1)) := by
    have := Finset.card_nsmul_le_sum (P.erase q₀)
      (fun h => ∑ j ∈ Finset.range σ.length, moveCost (sched h j) (sched h (j + 1)))
      (offlineCost C₀ σ) hOPTle
    rwa [hcardE, nsmul_eq_mul] at this
  have hsum2 : ∑ h ∈ P.erase q₀, ∑ j ∈ Finset.range σ.length,
      moveCost (sched h j) (sched h (j + 1))
      ≤ (∑ h ∈ P.erase q₀, moveCost C₀ (base h))
        + ∑ j ∈ Finset.range σ.length, dist (req j) (req (j + 1)) := by
    have h1 := Finset.sum_le_sum hschedcost
    rw [Finset.sum_add_distrib] at h1
    have h2 : ∑ h ∈ P.erase q₀, ∑ j ∈ Finset.range σ.length,
        moveCost (S h j) (S h (j + 1))
        = ∑ j ∈ Finset.range σ.length, dist (req j) (req (j + 1)) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => hstepcost j
    rw [h2] at h1
    exact h1
  have hsum3 : ∑ j ∈ Finset.range σ.length, dist (req j) (req (j + 1))
      ≤ ((σ.zip σ.tail).map (fun p => dist p.1 p.2)).sum + Δ := by
    cases hn : σ.length with
    | zero =>
      have hc : (0:ℝ) ≤ ((σ.zip σ.tail).map (fun p => dist p.1 p.2)).sum := by
        apply List.sum_nonneg
        intro x hx
        obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
        exact dist_nonneg
      simp only [Finset.range_zero, Finset.sum_empty]
      linarith
    | succ m =>
      rw [Finset.sum_range_succ']
      have h1 : ∀ i ∈ Finset.range m, dist (req (i + 1)) (req (i + 1 + 1))
          = dist (σ.getD i q₀) (σ.getD (i + 1) q₀) := by
        intro i _; rw [hreqS, hreqS]
      rw [Finset.sum_congr rfl h1]
      have h2 := consec_eq_range_sum q₀ σ
      rw [hn] at h2
      simp only [Nat.add_sub_cancel] at h2
      rw [← h2, hreq0]
      have h3 : dist q₀ (req 1) ≤ Δ := hΔ q₀ hq₀ _ (hreqP 1)
      linarith
  linarith [hsum1, hsum2, hsum3]
