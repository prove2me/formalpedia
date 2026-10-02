-- Prove2me | solution 1 for ProofsInTheBook.Chapter34.chapter34
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T16:13:09.844391+00:00
-- url     : https://prove2.me/submissions/c3d101bf-c78b-462d-868f-e04ae88d955e

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter34


/-!
# Chapter 34: The Dinitz problem

From "Proofs from THE BOOK":

**Galvin's theorem** (solving the Dinitz conjecture): For any assignment
of n-element color lists to the n² cells of an n×n array, there exists
a proper Latin square coloring (each cell gets a color from its list).

The book's proof uses the theory of list coloring for bipartite graphs,
specifically kernel-perfect orientations.
-/

namespace ProofsInTheBook.Chapter34















theorem dinitzOrient_orientedEdge {n : ℕ} :
    OrientedEdge (LatinConflict : Cell n → Cell n → Prop) dinitzOrient := by
  intro u v h
  exact h.1

theorem cyclicLatinValue_eq_of_same_row {n : ℕ} {a b : Cell n}
    (hrow : a.1 = b.1) (hval : cyclicLatinValue a = cyclicLatinValue b) :
    a.2 = b.2 := by
  have h : a.1 + a.2 = a.1 + b.2 := by
    simpa [cyclicLatinValue, hrow] using hval
  exact add_left_cancel h

theorem cyclicLatinValue_eq_of_same_col {n : ℕ} {a b : Cell n}
    (hcol : a.2 = b.2) (hval : cyclicLatinValue a = cyclicLatinValue b) :
    a.1 = b.1 := by
  have h : a.1 + a.2 = b.1 + a.2 := by
    simpa [cyclicLatinValue, hcol] using hval
  exact add_right_cancel h

theorem dinitzOrient_outNeighbors_card_lt {n : ℕ} (cell : Cell n) :
    (outNeighborsIn (Finset.univ : Finset (Cell n)) dinitzOrient cell).card < n := by
  classical
  let out := outNeighborsIn (Finset.univ : Finset (Cell n)) dinitzOrient cell
  let target := (Finset.univ : Finset (Fin n)).erase (cyclicLatinValue cell)
  have hmaps : Set.MapsTo cyclicLatinValue (out : Set (Cell n)) (target : Set (Fin n)) := by
    intro b hb
    have hb' : dinitzOrient cell b := by
      simpa [out, outNeighborsIn] using hb
    rcases hb' with ⟨_, hdir⟩
    apply Finset.mem_erase.mpr
    constructor
    · rcases hdir with ⟨_, hlt⟩ | ⟨_, hlt⟩
      · exact ne_of_gt hlt
      · exact ne_of_lt hlt
    · exact Finset.mem_univ _
  have hinj : Set.InjOn cyclicLatinValue (out : Set (Cell n)) := by
    intro b hb d hd hval
    have hb' : dinitzOrient cell b := by
      simpa [out, outNeighborsIn] using hb
    have hd' : dinitzOrient cell d := by
      simpa [out, outNeighborsIn] using hd
    rcases hb' with ⟨_, hbdir⟩
    rcases hd' with ⟨_, hddir⟩
    rcases hbdir with ⟨hbrow, hblt⟩ | ⟨hbcol, hblt⟩
    · rcases hddir with ⟨hdrow, hdlt⟩ | ⟨hdcol, hdlt⟩
      · have hrow : b.1 = d.1 := by exact hbrow.symm.trans hdrow
        have hcol : b.2 = d.2 := cyclicLatinValue_eq_of_same_row hrow hval
        exact Prod.ext hrow hcol
      · exfalso
        have : cyclicLatinValue d < cyclicLatinValue cell := hdlt
        rw [← hval] at this
        exact not_lt_of_ge hblt.le this
    · rcases hddir with ⟨hdrow, hdlt⟩ | ⟨hdcol, hdlt⟩
      · exfalso
        have : cyclicLatinValue cell < cyclicLatinValue d := hdlt
        rw [← hval] at this
        exact not_lt_of_ge hblt.le this
      · have hcol : b.2 = d.2 := by exact hbcol.symm.trans hdcol
        have hrow : b.1 = d.1 := cyclicLatinValue_eq_of_same_col hcol hval
        exact Prod.ext hrow hcol
  have hle : out.card ≤ target.card :=
    Finset.card_le_card_of_injOn cyclicLatinValue hmaps hinj
  have htarget : target.card = n - 1 := by
    simp [target]
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le cell.1.val) cell.1.isLt
  have houtcard : out.card =
      (outNeighborsIn (Finset.univ : Finset (Cell n)) dinitzOrient cell).card := rfl
  omega

theorem dinitzOrient_outNeighbors_lt_list_card {n : ℕ} {α : Type*}
    (lists : Cell n → Finset α) (hlists : ∀ cell, n ≤ (lists cell).card)
    (cell : Cell n) :
    (outNeighborsIn (Finset.univ : Finset (Cell n)) dinitzOrient cell).card <
      (lists cell).card :=
  lt_of_lt_of_le (dinitzOrient_outNeighbors_card_lt cell) (hlists cell)

















/-! ### Galvin's actual kernel-perfect list-coloring interface -/







/--
This is the correct replacement target for the false one-cell extension
premise: Galvin's induction colors a kernel all at once, then removes that
kernel and one color.
-/
theorem galvin_list_coloring_from_kernel_perfect_target
    {V α : Type*} [DecidableEq V] [DecidableEq α] [Inhabited α]
    (S : Finset V) (adj orient : V → V → Prop)
    [DecidableRel adj] [DecidableRel orient]
    (lists : V → Finset α)
    (_horient : OrientedEdge adj orient)
    (_hkernel : KernelPerfectOn S adj orient)
    (_hsize : ∀ v ∈ S, (outNeighborsIn S orient v).card < (lists v).card) :
    ∃ color : V → α, ListColoringOn S adj lists color := by
  classical
  let P : ℕ → Prop := fun m =>
    ∀ (S : Finset V) (lists : V → Finset α),
      S.card = m →
      KernelPerfectOn S adj orient →
      (∀ v ∈ S, (outNeighborsIn S orient v).card < (lists v).card) →
      ∃ color : V → α, ListColoringOn S adj lists color
  have hP : ∀ m, P m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro S lists hcard hkernel hsize
      by_cases hS : S.Nonempty
      · obtain ⟨v₀, hv₀⟩ := hS
        have hlist₀ : (lists v₀).Nonempty := by
          apply Finset.card_pos.mp
          exact lt_of_le_of_lt (Nat.zero_le _) (hsize v₀ hv₀)
        obtain ⟨c, hc⟩ := hlist₀
        let A : Finset V := S.filter fun v => c ∈ lists v
        have hAsub : A ⊆ S := Finset.filter_subset _ _
        have hAnonempty : A.Nonempty := ⟨v₀, by simp [A, hv₀, hc]⟩
        obtain ⟨K, hK⟩ := hkernel A hAsub hAnonempty
        rcases hK with ⟨hKsubA, hKind, hAbsorb⟩
        have hKsubS : K ⊆ S := fun x hx => hAsub (hKsubA hx)
        have hKnonempty : K.Nonempty := by
          obtain ⟨a, ha⟩ := hAnonempty
          by_cases haK : a ∈ K
          · exact ⟨a, haK⟩
          · obtain ⟨b, hbK, _⟩ := hAbsorb a ha haK
            exact ⟨b, hbK⟩
        let S' : Finset V := S \ K
        let lists' : V → Finset α := fun v => (lists v).erase c
        have hcardlt : S'.card < S.card := by
          have hcardK : 0 < K.card := Finset.card_pos.mpr hKnonempty
          have hKle : K.card ≤ S.card := Finset.card_le_card hKsubS
          have hsdiff := Finset.card_sdiff_of_subset hKsubS
          dsimp [S']
          rw [hsdiff]
          omega
        have hkernel' : KernelPerfectOn S' adj orient := by
          intro T hT hTne
          apply hkernel T ?_ hTne
          intro x hx
          exact (Finset.mem_sdiff.mp (hT hx)).1
        have hsize' : ∀ v ∈ S', (outNeighborsIn S' orient v).card < (lists' v).card := by
          intro v hvS'
          have hvS : v ∈ S := (Finset.mem_sdiff.mp hvS').1
          have hvnotK : v ∉ K := (Finset.mem_sdiff.mp hvS').2
          by_cases hcv : c ∈ lists v
          · have hvA : v ∈ A := by simp [A, hvS, hcv]
            obtain ⟨y, hyK, hvy⟩ := hAbsorb v hvA hvnotK
            have hsubOut : outNeighborsIn S' orient v ⊂ outNeighborsIn S orient v := by
              constructor
              · intro x hx
                simp [outNeighborsIn] at hx ⊢
                exact ⟨(Finset.mem_sdiff.mp hx.1).1, hx.2⟩
              · intro hsubReverse
                have hyOutS : y ∈ outNeighborsIn S orient v := by
                  simp [outNeighborsIn, hKsubS hyK, hvy]
                have hyNotOutS' : y ∉ outNeighborsIn S' orient v := by
                  intro hy
                  have hyS' : y ∈ S' := by
                    simpa [outNeighborsIn] using (Finset.mem_filter.mp hy).1
                  exact (Finset.mem_sdiff.mp hyS').2 hyK
                exact hyNotOutS' (hsubReverse hyOutS)
            have houtlt : (outNeighborsIn S' orient v).card < (outNeighborsIn S orient v).card :=
              Finset.card_lt_card hsubOut
            have hlistErase : (lists' v).card + 1 = (lists v).card := by
              dsimp [lists']
              exact Finset.card_erase_add_one hcv
            have hmain := hsize v hvS
            omega
          · have hsubOut : outNeighborsIn S' orient v ⊆ outNeighborsIn S orient v := by
              intro x hx
              simp [outNeighborsIn] at hx ⊢
              exact ⟨(Finset.mem_sdiff.mp hx.1).1, hx.2⟩
            have houtle : (outNeighborsIn S' orient v).card ≤ (outNeighborsIn S orient v).card :=
              Finset.card_le_card hsubOut
            have hlistEq : (lists' v).card = (lists v).card := by
              dsimp [lists']
              rw [Finset.erase_eq_of_notMem hcv]
            have hmain := hsize v hvS
            omega
        have hcardltm : S'.card < m := by omega
        obtain ⟨color', hcolor'⟩ := ih S'.card hcardltm S' lists' rfl hkernel' hsize'
        rcases hcolor' with ⟨hlist', hproper'⟩
        let color : V → α := fun v => if v ∈ K then c else color' v
        refine ⟨color, ?_⟩
        constructor
        · intro v hv
          by_cases hvK : v ∈ K
          · have hvA : v ∈ A := hKsubA hvK
            simpa [color, hvK, A] using (Finset.mem_filter.mp hvA).2
          · have hvS' : v ∈ S' := by simp [S', hv, hvK]
            have hvlist' := hlist' v hvS'
            simp [color, hvK]
            exact Finset.mem_of_mem_erase hvlist'
        · intro u hu v hv huv hne
          by_cases huK : u ∈ K <;> by_cases hvK : v ∈ K
          · exact False.elim (hne (hKind u huK v hvK huv))
          · have hvS' : v ∈ S' := by simp [S', hv, hvK]
            have hvlist' := hlist' v hvS'
            simp [color, huK, hvK]
            exact (Finset.ne_of_mem_erase hvlist').symm
          · have huS' : u ∈ S' := by simp [S', hu, huK]
            have hulist' := hlist' u huS'
            simp [color, huK, hvK]
            exact Finset.ne_of_mem_erase hulist'
          · have huS' : u ∈ S' := by simp [S', hu, huK]
            have hvS' : v ∈ S' := by simp [S', hv, hvK]
            simp [color, huK, hvK]
            exact hproper' u huS' v hvS' huv hne
      · refine ⟨fun _ => default, ?_⟩
        constructor
        · intro v hv
          exact False.elim (hS ⟨v, hv⟩)
        · intro u hu _ _ _ _
          exact False.elim (hS ⟨u, hu⟩)
  exact hP S.card S lists rfl _hkernel _hsize

/--
Correct Galvin interface specialized to the Dinitz conflict graph: once an
orientation is known to be kernel-perfect and to have outdegree below each
list size, a Dinitz list coloring follows.
-/
theorem dinitzSolution_of_kernel_perfect_orientation {n : ℕ} {α : Type*}
    [DecidableEq α] [Inhabited α]
    (lists : Cell n → Finset α)
    (orient : Cell n → Cell n → Prop) [DecidableRel orient]
    (horient : OrientedEdge LatinConflict orient)
    (hkernel : KernelPerfectOn (Finset.univ : Finset (Cell n)) LatinConflict orient)
    (hsize : ∀ cell : Cell n,
      (outNeighborsIn (Finset.univ : Finset (Cell n)) orient cell).card < (lists cell).card) :
    ∃ color : Cell n → α, DinitzSolution lists color := by
  classical
  obtain ⟨color, hcolor⟩ :=
    galvin_list_coloring_from_kernel_perfect_target
      (S := (Finset.univ : Finset (Cell n))) (adj := LatinConflict) (orient := orient)
      (lists := lists) horient hkernel (by intro v _; exact hsize v)
  rcases hcolor with ⟨hlist, hproper⟩
  refine ⟨color, ?_⟩
  constructor
  · intro cell
    exact hlist cell (Finset.mem_univ cell)
  · intro a b hab
    exact hproper a (Finset.mem_univ a) b (Finset.mem_univ b) hab hab.1

/-! ### Stable matchings give Galvin kernels for the Dinitz orientation -/







theorem isKernelIn_of_stableMatching {n : ℕ} {A M : Finset (Cell n)}
    (hstable : StableMatching A M) :
    IsKernelIn A M LatinConflict dinitzOrient := by
  rcases hstable with ⟨hmatching, hdom⟩
  rcases hmatching with ⟨hsub, hind⟩
  exact ⟨hsub, hind, hdom⟩

private lemma exists_row_cyclic_max {n : ℕ} {A : Finset (Cell n)} {x : Cell n}
    (hx : x ∈ A) :
    ∃ y ∈ A, y.1 = x.1 ∧ cyclicLatinValue x ≤ cyclicLatinValue y ∧
      ∀ z ∈ A, z.1 = x.1 → cyclicLatinValue z ≤ cyclicLatinValue y := by
  classical
  let R : Finset (Cell n) := A.filter fun z => z.1 = x.1
  have hxR : x ∈ R := by
    simp [R, hx]
  obtain ⟨y, hymax⟩ := R.exists_maximalFor cyclicLatinValue ⟨x, hxR⟩
  have hyR : y ∈ R := hymax.1
  have hyA : y ∈ A := (Finset.mem_filter.mp hyR).1
  have hyrow : y.1 = x.1 := (Finset.mem_filter.mp hyR).2
  refine ⟨y, hyA, hyrow, ?_, ?_⟩
  · have hx_le_or : cyclicLatinValue x ≤ cyclicLatinValue y ∨
        cyclicLatinValue y ≤ cyclicLatinValue x := le_total _ _
    rcases hx_le_or with hxy | hyx
    · exact hxy
    · exact hymax.2 hxR hyx
  · intro z hzA hzrow
    have hzR : z ∈ R := by
      simp [R, hzA, hzrow]
    have hz_le_or : cyclicLatinValue z ≤ cyclicLatinValue y ∨
        cyclicLatinValue y ≤ cyclicLatinValue z := le_total _ _
    rcases hz_le_or with hzy | hyz
    · exact hzy
    · exact hymax.2 hzR hyz

private lemma exists_col_cyclic_max {n : ℕ} {A : Finset (Cell n)} {x : Cell n}
    (hx : x ∈ A) :
    ∃ y ∈ A, y.2 = x.2 ∧ cyclicLatinValue x ≤ cyclicLatinValue y ∧
      ∀ z ∈ A, z.2 = x.2 → cyclicLatinValue z ≤ cyclicLatinValue y := by
  classical
  let C : Finset (Cell n) := A.filter fun z => z.2 = x.2
  have hxC : x ∈ C := by
    simp [C, hx]
  obtain ⟨y, hymax⟩ := C.exists_maximalFor cyclicLatinValue ⟨x, hxC⟩
  have hyC : y ∈ C := hymax.1
  have hyA : y ∈ A := (Finset.mem_filter.mp hyC).1
  have hycol : y.2 = x.2 := (Finset.mem_filter.mp hyC).2
  refine ⟨y, hyA, hycol, ?_, ?_⟩
  · have hx_le_or : cyclicLatinValue x ≤ cyclicLatinValue y ∨
        cyclicLatinValue y ≤ cyclicLatinValue x := le_total _ _
    rcases hx_le_or with hxy | hyx
    · exact hxy
    · exact hymax.2 hxC hyx
  · intro z hzA hzcol
    have hzC : z ∈ C := by
      simp [C, hzA, hzcol]
    have hz_le_or : cyclicLatinValue z ≤ cyclicLatinValue y ∨
        cyclicLatinValue y ≤ cyclicLatinValue z := le_total _ _
    rcases hz_le_or with hzy | hyz
    · exact hzy
    · exact hymax.2 hzC hyz

/--
The remaining hard Galvin lemma: every finite induced subgraph of the Dinitz
orientation has a stable matching. This is the stable-marriage part of the
book proof.
-/
theorem stableMatching_exists {n : ℕ} (A : Finset (Cell n)) :
    ∃ M : Finset (Cell n), StableMatching A M := by
  classical
  let P : ℕ → Prop := fun m => ∀ A : Finset (Cell n), A.card = m →
    ∃ M : Finset (Cell n), StableMatching A M
  have hP : ∀ m, P m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro A hcard
      by_cases hA : A.Nonempty
      · let T : Finset (Cell n) :=
          A.filter fun x =>
            ∀ y ∈ A, y.1 = x.1 → cyclicLatinValue y ≤ cyclicLatinValue x
        by_cases hTind : ∀ u ∈ T, ∀ v ∈ T, LatinConflict u v → u = v
        · refine ⟨T, ?_⟩
          constructor
          · constructor
            · exact Finset.filter_subset _ _
            · exact hTind
          · intro cell hcellA hcellT
            obtain ⟨y, hyA, hyrow, _, hymax⟩ := exists_row_cyclic_max (A := A) hcellA
            have hyT : y ∈ T := by
              apply Finset.mem_filter.mpr
              constructor
              · exact hyA
              intro z hzA hzrow
              exact hymax z hzA (hzrow.trans hyrow)
            have hlt : cyclicLatinValue cell < cyclicLatinValue y := by
              by_contra hnot
              have hyle : cyclicLatinValue y ≤ cyclicLatinValue cell := le_of_not_gt hnot
              have hcellTin : cell ∈ T := by
                apply Finset.mem_filter.mpr
                constructor
                · exact hcellA
                intro z hzA hzrow
                exact (hymax z hzA hzrow).trans hyle
              exact hcellT hcellTin
            refine ⟨y, hyT, ?_⟩
            have hne : cell ≠ y := by
              intro hcy
              subst cell
              exact (lt_irrefl (cyclicLatinValue y)) hlt
            exact ⟨⟨hne, Or.inl hyrow.symm⟩, Or.inl ⟨hyrow.symm, hlt⟩⟩
        · push Not at hTind
          obtain ⟨u, huT, v, hvT, huvconf, huvne⟩ := hTind
          have huA : u ∈ A := (Finset.mem_filter.mp huT).1
          have hvA : v ∈ A := (Finset.mem_filter.mp hvT).1
          have huMax : ∀ y ∈ A, y.1 = u.1 → cyclicLatinValue y ≤ cyclicLatinValue u :=
            (Finset.mem_filter.mp huT).2
          have hvMax : ∀ y ∈ A, y.1 = v.1 → cyclicLatinValue y ≤ cyclicLatinValue v :=
            (Finset.mem_filter.mp hvT).2
          obtain ⟨hune, hrowcol⟩ := huvconf
          have hcoluv : u.2 = v.2 := by
            rcases hrowcol with hrow | hcol
            · have huvle : cyclicLatinValue u ≤ cyclicLatinValue v := hvMax u huA hrow
              have hvule : cyclicLatinValue v ≤ cyclicLatinValue u := huMax v hvA hrow.symm
              have hval : cyclicLatinValue u = cyclicLatinValue v := le_antisymm huvle hvule
              have hcol' : u.2 = v.2 := cyclicLatinValue_eq_of_same_row hrow hval
              exact hcol'
            · exact hcol
          have hvalne : cyclicLatinValue u ≠ cyclicLatinValue v := by
            intro hval
            have hrow' : u.1 = v.1 := cyclicLatinValue_eq_of_same_col hcoluv hval
            exact hune (Prod.ext hrow' hcoluv)
          have hpair :
              ∃ low high : Cell n,
                low ∈ T ∧ high ∈ T ∧ low.2 = high.2 ∧
                  cyclicLatinValue low < cyclicLatinValue high := by
            rcases lt_or_gt_of_ne hvalne with huvlt | hvult
            · exact ⟨u, v, huT, hvT, hcoluv, huvlt⟩
            · exact ⟨v, u, hvT, huT, hcoluv.symm, hvult⟩
          obtain ⟨low, high, hlowT, hhighT, hlowhighcol, hlowhighlt⟩ := hpair
          have hlowA : low ∈ A := (Finset.mem_filter.mp hlowT).1
          have hhighA : high ∈ A := (Finset.mem_filter.mp hhighT).1
          have hlowMax : ∀ y ∈ A, y.1 = low.1 → cyclicLatinValue y ≤ cyclicLatinValue low :=
            (Finset.mem_filter.mp hlowT).2
          obtain ⟨v₀, hv₀A, hv₀col, _, hv₀max⟩ := exists_col_cyclic_max (A := A) hlowA
          have hhighle : cyclicLatinValue high ≤ cyclicLatinValue v₀ :=
            hv₀max high hhighA hlowhighcol.symm
          have hlowltv₀ : cyclicLatinValue low < cyclicLatinValue v₀ :=
            hlowhighlt.trans_le hhighle
          have hlow_ne_v₀ : low ≠ v₀ := by
            intro h
            subst low
            exact (lt_irrefl (cyclicLatinValue v₀)) hlowltv₀
          have hcardlt : (A.erase v₀).card < m := by
            rw [← hcard]
            exact Finset.card_erase_lt_of_mem hv₀A
          obtain ⟨K, hKstable⟩ := ih (A.erase v₀).card hcardlt (A.erase v₀) rfl
          rcases hKstable with ⟨hKmatch, hKdom⟩
          rcases hKmatch with ⟨hKsubErase, hKind⟩
          refine ⟨K, ?_⟩
          constructor
          · constructor
            · intro x hxK
              exact Finset.mem_of_mem_erase (hKsubErase hxK)
            · exact hKind
          · intro cell hcellA hcellK
            by_cases hcellv₀ : cell = v₀
            · subst cell
              have hv₀K : v₀ ∉ K := by
                intro hv₀K
                exact (Finset.mem_erase.mp (hKsubErase hv₀K)).1 rfl
              by_cases hlowK : low ∈ K
              · refine ⟨low, hlowK, ?_⟩
                have hne : v₀ ≠ low := by
                  intro h
                  subst v₀
                  exact (lt_irrefl (cyclicLatinValue low)) hlowltv₀
                exact ⟨⟨hne, Or.inr hv₀col⟩, Or.inr ⟨hv₀col, hlowltv₀⟩⟩
              · have hlowErase : low ∈ A.erase v₀ := by
                  simp [hlowA, hlow_ne_v₀]
                obtain ⟨k, hkK, hlowk⟩ := hKdom low hlowErase hlowK
                have hkA : k ∈ A := Finset.mem_of_mem_erase (hKsubErase hkK)
                rcases hlowk with ⟨_, hdir⟩
                rcases hdir with ⟨hkrow, hlowltk⟩ | ⟨hkcol, hkltlow⟩
                · exfalso
                  exact not_lt_of_ge (hlowMax k hkA hkrow.symm) hlowltk
                · refine ⟨k, hkK, ?_⟩
                  have hv₀kcol : v₀.2 = k.2 := hv₀col.trans hkcol
                  have hkltv₀ : cyclicLatinValue k < cyclicLatinValue v₀ :=
                    hkltlow.trans hlowltv₀
                  have hne : v₀ ≠ k := by
                    intro h
                    subst v₀
                    exact (lt_irrefl (cyclicLatinValue k)) hkltv₀
                  exact ⟨⟨hne, Or.inr hv₀kcol⟩, Or.inr ⟨hv₀kcol, hkltv₀⟩⟩
            · have hcellErase : cell ∈ A.erase v₀ := by
                simp [hcellA, hcellv₀]
              exact hKdom cell hcellErase hcellK
      · refine ⟨∅, ?_⟩
        constructor
        · constructor
          · intro x hx
            simp at hx
          · intro u hu
            simp at hu
        · intro cell hcellA _
          exact False.elim (hA ⟨cell, hcellA⟩)
  exact hP A.card A rfl

theorem dinitzOrient_kernelPerfectOn {n : ℕ} :
    KernelPerfectOn (Finset.univ : Finset (Cell n)) LatinConflict dinitzOrient := by
  intro A hA hAne
  obtain ⟨M, hM⟩ := stableMatching_exists A
  exact ⟨M, isKernelIn_of_stableMatching hM⟩

theorem dinitzSolution_of_dinitzOrient {n : ℕ} {α : Type*}
    [DecidableEq α] [Inhabited α]
    (lists : Cell n → Finset α) (hlists : ∀ cell, n ≤ (lists cell).card) :
    ∃ color : Cell n → α, DinitzSolution lists color :=
  dinitzSolution_of_kernel_perfect_orientation lists dinitzOrient
    dinitzOrient_orientedEdge dinitzOrient_kernelPerfectOn
    (dinitzOrient_outNeighbors_lt_list_card lists hlists)

/--
Galvin's theorem (the Dinitz conjecture): given an n×n array where each cell
has a list of at least n colors, there exists a proper Latin coloring respecting
all lists. The proof constructs a kernel-perfect orientation from the list
orderings and applies the greedy extension step.
-/
theorem galvin_theorem {n : ℕ} {α : Type*} [DecidableEq α]
    (lists : Cell n → Finset α)
    (hlists : ∀ cell, n ≤ (lists cell).card) :
    ∃ color : Cell n → α, DinitzSolution lists color := by
  classical
  by_cases hn : n = 0
  · subst n
    let color : Cell 0 → α := fun cell => Fin.elim0 cell.1
    refine ⟨color, ?_⟩
    constructor
    · intro cell
      exact Fin.elim0 cell.1
    · intro a _ _
      exact Fin.elim0 a.1
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let z : Fin n := ⟨0, hnpos⟩
    have hcard_pos : 0 < (lists (z, z)).card := lt_of_lt_of_le hnpos (hlists (z, z))
    haveI : Inhabited α := ⟨Classical.choose (Finset.card_pos.mp hcard_pos)⟩
    exact dinitzSolution_of_dinitzOrient lists hlists



end ProofsInTheBook.Chapter34

open ProofsInTheBook.Chapter34

theorem solution {n : ℕ} {α : Type*} [DecidableEq α]
    (lists : Cell n → Finset α)
    (hlists : ∀ cell, n ≤ (lists cell).card) :
    ∃ color : Cell n → α, DinitzSolution lists color :=
  galvin_theorem lists hlists
